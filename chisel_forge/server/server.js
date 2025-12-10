import express from 'express';
import cors from 'cors';
import { exec } from 'child_process';
import { promisify } from 'util';
import fs from 'fs/promises';
import path from 'path';
import { fileURLToPath } from 'url';
import { v4 as uuidv4 } from 'uuid';
import dotenv from 'dotenv';

// Load environment variables
dotenv.config();

const execAsync = promisify(exec);
const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

// Compilation queue and cache for speed
const compilationQueue = [];
let isCompiling = false;
const compilationCache = new Map(); // cache results by code hash

const app = express();
const PORT = process.env.PORT || 3001;

// Path to the chisel repository submodule
const CHISEL_ROOT = process.env.CHISEL_ROOT || path.resolve(__dirname, '../chisel');
const CHISEL_SRC = path.join(CHISEL_ROOT, 'src/main/scala/examples');
const CHISEL_GENERATED = path.join(CHISEL_ROOT, 'generated');

app.use(cors());
app.use(express.json({ limit: '10mb' }));

// Health check
app.get('/api/health', (req, res) => {
  res.json({ status: 'ok', message: 'ChiselForge compilation server running' });
});

// Main compilation endpoint
app.post('/api/compile', async (req, res) => {
  const { code, moduleName = 'UserModule', config = {} } = req.body;
  
  if (!code) {
    return res.status(400).json({ error: 'No code provided' });
  }
  
  // Security: Validate code doesn't contain malicious patterns
  if (code.includes('sys.process') || code.includes('Runtime.getRuntime') || code.includes('ProcessBuilder')) {
    return res.status(400).json({ error: 'Code contains prohibited system calls' });
  }
  
  // Check cache first for speed
  const cacheKey = Buffer.from(code + moduleName + JSON.stringify(config)).toString('base64').slice(0, 32);
  if (compilationCache.has(cacheKey)) {
    console.log('✓ Cache hit! Returning cached result');
    return res.json(compilationCache.get(cacheKey));
  }

  const sessionId = uuidv4();
  
  // Use the module name provided by the frontend
  const actualClassName = moduleName || 'UserModule';
  const userFile = path.join(CHISEL_SRC, `${actualClassName}.scala`);
  
  console.log(`[${sessionId}] Compilation request for module: ${moduleName}`);
  console.log(`[${sessionId}] Using module name: ${actualClassName}`);

  try {
    // Step 1: Write user code to file (ensure it's in examples package)
    let processedCode = code;
    
    // Ensure the code is in the examples package
    if (!processedCode.includes('package examples')) {
      processedCode = 'package examples\n' + processedCode;
    }
    
    await fs.writeFile(userFile, processedCode, 'utf-8');
    console.log(`[${sessionId}] Wrote code to ${userFile}`);

    // Step 2: Write generation config
    const generationConfig = {
      module: actualClassName,
      mode: config.mode || 'verification',
      layers: config.layers || 'inline',
      preserve_values: config.preserve_values || 'named',
      randomization: config.randomization || 'disable',
      run_formal: config.run_formal || 'no'
    };
    
    const configPath = path.join(CHISEL_ROOT, 'generation_config.json');
    await fs.writeFile(configPath, JSON.stringify(generationConfig, null, 2));
    console.log(`[${sessionId}] Wrote config: ${JSON.stringify(generationConfig)}`);

    // Step 3: Run SBT compilation with speed optimizations
    console.log(`[${sessionId}] Starting Chisel elaboration...`);
    
    // Load direnv environment if available
    let sbtCommand = `cd ${CHISEL_ROOT} && eval "$(direnv export bash 2>/dev/null)" && make generate MODULE=${actualClassName}`;
    
    let stdout = '';
    let stderr = '';
    
    try {
      const result = await execAsync(sbtCommand, {
        timeout: 60000, // 1 minute (faster timeout)
        maxBuffer: 10 * 1024 * 1024, // 10MB buffer
        shell: '/bin/bash',
        env: { 
          ...process.env, 
          JAVA_OPTS: '-Xmx2G -XX:+UseG1GC -XX:MaxGCPauseMillis=100',
          SBT_OPTS: '-Dsbt.log.noformat=true'
        }
      });
      stdout = result.stdout;
      stderr = result.stderr;
      console.log(`[${sessionId}] Compilation successful`);
    } catch (execError) {
      // Even if make fails, we might have useful error messages
      stdout = execError.stdout || '';
      stderr = execError.stderr || '';
      console.error(`[${sessionId}] Compilation failed:`, stderr);
    }

    // Step 4: Try to read generated files
    const moduleDir = path.join(CHISEL_GENERATED, actualClassName);
    const verilogPath = path.join(moduleDir, `${actualClassName}.sv`);
    
    let verilog = null;
    let firrtl = null;
    let compilationSuccess = false;

    try {
      verilog = await fs.readFile(verilogPath, 'utf-8');
      compilationSuccess = true;
      console.log(`[${sessionId}] Successfully read Verilog output`);
    } catch (readError) {
      console.warn(`[${sessionId}] Could not read Verilog: ${readError.message}`);
    }

    // Try to read FIRRTL if it exists
    const firrtlPath = path.join(moduleDir, `${actualClassName}.fir`);
    try {
      firrtl = await fs.readFile(firrtlPath, 'utf-8');
    } catch (e) {
      // FIRRTL might not be saved, that's okay
    }

    // Step 5: Clean up temporary files
    try {
      await fs.unlink(userFile);
      console.log(`[${sessionId}] Cleaned up ${actualClassName}.scala`);
    } catch (e) {
      console.warn(`[${sessionId}] Could not clean up: ${e.message}`);
    }

    // Step 6: Parse errors from output
    const errors = parseCompilationErrors(stdout + '\n' + stderr);

    // Step 7: Return results with caching
    if (compilationSuccess && verilog) {
      const result = {
        success: true,
        verilog,
        firrtl,
        stdout,
        stderr,
        errors: errors.length > 0 ? errors : null,
        moduleName: actualClassName
      };
      
      // Cache successful result (limit to 50)
      compilationCache.set(cacheKey, result);
      if (compilationCache.size > 50) {
        const firstKey = compilationCache.keys().next().value;
        compilationCache.delete(firstKey);
      }
      
      res.json(result);
    } else {
      res.status(400).json({
        success: false,
        error: 'Compilation failed',
        stdout,
        stderr,
        errors
      });
    }

  } catch (error) {
    console.error(`[${sessionId}] Server error:`, error);
    
    // Clean up on error
    try {
      await fs.unlink(userFile);
    } catch (e) {
      // Ignore cleanup errors
    }

    res.status(500).json({
      success: false,
      error: error.message,
      stack: process.env.NODE_ENV === 'development' ? error.stack : undefined
    });
  }
});

// Helper function to parse compilation errors
function parseCompilationErrors(output) {
  const errors = [];
  const errorPattern = /\[error\]\s+(.+?)(?:\n|$)/g;
  const locationPattern = /(\S+\.scala):(\d+):(\d+):/;
  
  let match;
  while ((match = errorPattern.exec(output)) !== null) {
    const errorLine = match[1];
    const locationMatch = errorLine.match(locationPattern);
    
    errors.push({
      message: errorLine,
      file: locationMatch ? locationMatch[1] : null,
      line: locationMatch ? parseInt(locationMatch[2]) : null,
      column: locationMatch ? parseInt(locationMatch[3]) : null
    });
  }
  
  return errors;
}

// List available example modules
app.get('/api/examples', async (req, res) => {
  try {
    // These are the working modules from the chisel repository
    const examples = [
      {
        name: 'Adder',
        file: 'Examples.scala',
        description: 'Simple 4-bit adder',
        hasParameters: false,
        parameters: ''
      },
      {
        name: 'Counter',
        file: 'Examples.scala',
        description: 'Simple counter with enable',
        hasParameters: false,
        parameters: ''
      },
      {
        name: 'Mux2to1',
        file: 'Examples.scala',
        description: 'Parameterized 2-to-1 multiplexer',
        hasParameters: true,
        parameters: 'width: Int = 8'
      },
      {
        name: 'SimpleALU',
        file: 'Examples.scala',
        description: 'Simple ALU with ADD/SUB/AND/OR operations',
        hasParameters: false,
        parameters: ''
      },
      {
        name: 'PWMLEDAXI',
        file: 'PWMLEDAXI.scala',
        description: 'PWM LED controller with AXI interface',
        hasParameters: true,
        parameters: 'pwmFrequency: Int, pwmWidth: Int, addrWidth: Int, dataWidth: Int, axiDataWidth: Int, inlineVerification: Boolean'
      },
      {
        name: 'AbstractedPWMLEDAXI',
        file: 'PWMLEDAXI.scala',
        description: 'Abstracted PWM LED controller with AXI',
        hasParameters: true,
        parameters: 'pwmFrequency: Int, pwmWidth: Int, addrWidth: Int, dataWidth: Int, axiDataWidth: Int'
      }
    ];
    
    res.json({ examples });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

// Get content of an example file
app.get('/api/examples/:name', async (req, res) => {
  try {
    const fileName = `${req.params.name}.scala`;
    const filePath = path.join(CHISEL_SRC, fileName);
    const content = await fs.readFile(filePath, 'utf-8');
    res.json({ name: req.params.name, content });
  } catch (error) {
    res.status(404).json({ error: 'Example not found' });
  }
});

// Formal verification endpoint using EBMC
app.post('/api/verify', async (req, res) => {
  const { moduleName, ebmcParams = {} } = req.body;
  
  if (!moduleName) {
    return res.status(400).json({ error: 'No module name provided' });
  }
  
  const sessionId = uuidv4();
  console.log(`[${sessionId}] Verification request for ${moduleName}`);
  console.log(`[${sessionId}] EBMC params:`, JSON.stringify(ebmcParams, null, 2));
  
  try {
    const moduleDir = path.join(CHISEL_GENERATED, moduleName);
    const svFile = path.join(moduleDir, `${moduleName}.sv`);
    
    // Check if Verilog file exists
    try {
      await fs.access(svFile);
    } catch (err) {
      return res.status(400).json({ 
        error: 'Module not compiled yet',
        message: `Please compile ${moduleName} first before verification`
      });
    }
    
    // Use EBMC_BIN environment variable or default
    const ebmcBin = process.env.EBMC_BIN || 'ebmc';
    
    // Pass EBMC params as JSON to the verification script
    const paramsJson = JSON.stringify(ebmcParams);
    const paramsBase64 = Buffer.from(paramsJson).toString('base64');
    
    // Run the formal verification script with params
    const verifyCommand = `cd ${CHISEL_ROOT} && EBMC_BIN=${ebmcBin} EBMC_PARAMS='${paramsBase64}' ./scripts/run_formal.sh ${moduleName}`;
    
    console.log(`[${sessionId}] Running: ${verifyCommand}`);
    
    let stdout = '';
    let stderr = '';
    let exitCode = 0;
    
    try {
      const result = await execAsync(verifyCommand, {
        timeout: 300000, // 5 minutes for verification
        maxBuffer: 50 * 1024 * 1024, // 50MB buffer for large outputs
        shell: '/bin/bash',
        env: {
          ...process.env,
          EBMC_BIN: ebmcBin,
          EBMC_PARAMS: paramsBase64
        }
      });
      stdout = result.stdout;
      stderr = result.stderr;
    } catch (execError) {
      // EBMC returns non-zero exit code when properties fail, but output is still valid
      stdout = execError.stdout || '';
      stderr = execError.stderr || '';
      exitCode = execError.code || 1;
      console.log(`[${sessionId}] EBMC exited with code ${exitCode} (may have refuted properties)`);
    }
    
    // Parse results from EBMC output
    const results = parseVerificationResults(stdout);
    
    // Check if VCD file was generated
    let vcdFile = null;
    if (ebmcParams.vcd) {
      const vcdPath = path.join(moduleDir, ebmcParams.vcd);
      try {
        await fs.access(vcdPath);
        vcdFile = ebmcParams.vcd;
        console.log(`[${sessionId}] VCD file generated: ${vcdFile}`);
      } catch (err) {
        console.log(`[${sessionId}] VCD file not found at ${vcdPath}`);
      }
    }
    
    res.json({
      success: true,
      moduleName,
      ebmcParams,
      exitCode,
      results,
      vcdFile,
      stdout,
      stderr
    });
    
  } catch (error) {
    console.error(`[${sessionId}] Verification error:`, error);
    res.status(500).json({
      success: false,
      error: error.message
    });
  }
});

// Parse EBMC verification results
function parseVerificationResults(output) {
  const results = {
    proved: [],
    failed: [],
    inconclusive: [],
    unsupported: []
  };
  
  // Parse the ** Results: section
  const resultsSection = output.split('** Results:')[1];
  if (!resultsSection) return results;
  
  const lines = resultsSection.split('\n');
  for (const line of lines) {
    if (line.includes('PROVED')) {
      const match = line.match(/\[([\w$.]+)\]\s+(.*?):\s+PROVED/);
      if (match) {
        results.proved.push({ property: match[1], description: match[2] });
      }
    } else if (line.includes('FAILED') || line.includes('REFUTED')) {
      const match = line.match(/\[([\w$.]+)\]\s+(.*?):\s+(FAILED|REFUTED)/);
      if (match) {
        results.failed.push({ property: match[1], description: match[2] });
      }
    } else if (line.includes('INCONCLUSIVE')) {
      const match = line.match(/\[([\w$.]+)\]\s+(.*?):\s+INCONCLUSIVE/);
      if (match) {
        results.inconclusive.push({ property: match[1], description: match[2] });
      }
    } else if (line.includes('UNSUPPORTED')) {
      const match = line.match(/\[([\w$.]+)\]\s+(.*?):\s+UNSUPPORTED/);
      if (match) {
        results.unsupported.push({ property: match[1], description: match[2] });
      }
    }
  }
  
  return results;
}

app.listen(PORT, async () => {
  console.log(`ChiselForge compilation server listening on port ${PORT}`);
  console.log(`Chisel root: ${CHISEL_ROOT}`);
  
  // Verify chisel directory exists
  try {
    await fs.access(CHISEL_ROOT);
    await fs.access(path.join(CHISEL_ROOT, 'tools/sbt/bin/sbt'));
    console.log(`✓ Chisel tools found at ${CHISEL_ROOT}`);
  } catch (err) {
    console.error(`✗ ERROR: Chisel not found at ${CHISEL_ROOT}`);
    console.error(`  Please set CHISEL_ROOT environment variable or run 'make setup' in chisel directory`);
    console.error(`  Example: CHISEL_ROOT=/path/to/chisel npm start`);
  }
  
  console.log(`API endpoints:`);
  console.log(`  GET  /api/health`);
  console.log(`  POST /api/compile`);
  console.log(`  POST /api/verify`);
  console.log(`  GET  /api/examples`);
  console.log(`  GET  /api/examples/:name`);
  console.log(`  GET  /api/files`);
  console.log(`  POST /api/files/upload`);
  console.log(`  GET  /api/files/:fileName`);
  console.log(`  DELETE /api/files/:fileName`);
  console.log(`  POST /api/files/rename`);
  console.log(`  GET  /api/vcd/:moduleName/:fileName`);
});

// File management endpoints

// List files in workspace
app.get('/api/files', async (req, res) => {
  try {
    const files = await fs.readdir(CHISEL_SRC);
    const scalaFiles = await Promise.all(
      files
        .filter(f => f.endsWith('.scala'))
        .map(async (f) => {
          const filePath = path.join(CHISEL_SRC, f);
          const stats = await fs.stat(filePath);
          return {
            name: f,
            path: `examples/${f}`,
            size: stats.size,
            modified: stats.mtime
          };
        })
    );
    
    res.json({ files: scalaFiles });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

// Upload a file
app.post('/api/files/upload', async (req, res) => {
  const { fileName, content } = req.body;
  
  if (!fileName || !content) {
    return res.status(400).json({ error: 'fileName and content required' });
  }
  
  // Security: validate filename
  if (fileName.includes('..') || fileName.includes('/')) {
    return res.status(400).json({ error: 'Invalid file name' });
  }
  
  if (!fileName.endsWith('.scala')) {
    return res.status(400).json({ error: 'Only .scala files allowed' });
  }
  
  try {
    const filePath = path.join(CHISEL_SRC, fileName);
    await fs.writeFile(filePath, content, 'utf-8');
    
    res.json({ 
      success: true, 
      message: `File ${fileName} uploaded successfully`,
      fileName 
    });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

// Download a file
app.get('/api/files/:fileName', async (req, res) => {
  const { fileName } = req.params;
  
  // Security: validate filename
  if (fileName.includes('..') || fileName.includes('/')) {
    return res.status(400).json({ error: 'Invalid file name' });
  }
  
  try {
    const filePath = path.join(CHISEL_SRC, fileName);
    const content = await fs.readFile(filePath, 'utf-8');
    const stats = await fs.stat(filePath);
    
    res.json({ 
      fileName,
      content,
      size: stats.size,
      modified: stats.mtime
    });
  } catch (error) {
    res.status(404).json({ error: 'File not found' });
  }
});

// Delete a file
app.delete('/api/files/:fileName', async (req, res) => {
  const { fileName } = req.params;
  
  // Security: validate filename
  if (fileName.includes('..') || fileName.includes('/')) {
    return res.status(400).json({ error: 'Invalid file name' });
  }
  
  // Prevent deletion of example files
  const examples = ['PWMLEDAXI.scala', 'ShiftRegister.scala', 'Adder.scala', 'Empty.scala'];
  if (examples.includes(fileName)) {
    return res.status(400).json({ error: 'Cannot delete example files' });
  }
  
  try {
    const filePath = path.join(CHISEL_SRC, fileName);
    await fs.unlink(filePath);
    
    res.json({ 
      success: true, 
      message: `File ${fileName} deleted successfully` 
    });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

// Rename a file
app.post('/api/files/rename', async (req, res) => {
  const { oldName, newName } = req.body;
  
  if (!oldName || !newName) {
    return res.status(400).json({ error: 'oldName and newName required' });
  }
  
  // Security: validate filenames
  if (oldName.includes('..') || oldName.includes('/') || 
      newName.includes('..') || newName.includes('/')) {
    return res.status(400).json({ error: 'Invalid file name' });
  }
  
  if (!newName.endsWith('.scala')) {
    return res.status(400).json({ error: 'Only .scala files allowed' });
  }
  
  // Prevent renaming of example files
  const examples = ['PWMLEDAXI.scala', 'ShiftRegister.scala', 'Adder.scala', 'Empty.scala'];
  if (examples.includes(oldName)) {
    return res.status(400).json({ error: 'Cannot rename example files' });
  }
  
  try {
    const oldPath = path.join(CHISEL_SRC, oldName);
    const newPath = path.join(CHISEL_SRC, newName);
    await fs.rename(oldPath, newPath);
    
    res.json({ 
      success: true, 
      message: `File renamed from ${oldName} to ${newName}`,
      newName
    });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

// Download VCD file endpoint
app.get('/api/vcd/:moduleName/:fileName', async (req, res) => {
  const { moduleName, fileName } = req.params;
  
  // Security: validate inputs
  if (moduleName.includes('..') || moduleName.includes('/') ||
      fileName.includes('..') || fileName.includes('/')) {
    return res.status(400).json({ error: 'Invalid module or file name' });
  }
  
  if (!fileName.endsWith('.vcd')) {
    return res.status(400).json({ error: 'Only VCD files can be downloaded' });
  }
  
  try {
    const vcdPath = path.join(CHISEL_GENERATED, moduleName, fileName);
    await fs.access(vcdPath);
    
    // Set headers for file download
    res.setHeader('Content-Type', 'application/octet-stream');
    res.setHeader('Content-Disposition', `attachment; filename="${fileName}"`);
    
    const fileContent = await fs.readFile(vcdPath);
    res.send(fileContent);
  } catch (error) {
    res.status(404).json({ error: 'VCD file not found' });
  }
});

