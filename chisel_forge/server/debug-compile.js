#!/usr/bin/env node

/**
 * ChiselForge Debug CLI
 * 
 * Test compilation flow without running the full web server.
 * This helps debug backend compilation issues faster.
 */

import fs from 'fs/promises';
import path from 'path';
import { exec } from 'child_process';
import { promisify } from 'util';
import { fileURLToPath } from 'url';

const execAsync = promisify(exec);
const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

const CHISEL_ROOT = process.env.CHISEL_ROOT || path.resolve(__dirname, '../chisel');
const CHISEL_SRC = path.join(CHISEL_ROOT, 'src/main/scala/examples');
const CHISEL_GENERATED = path.join(CHISEL_ROOT, 'generated');

// Color output
const colors = {
  reset: '\x1b[0m',
  bright: '\x1b[1m',
  red: '\x1b[31m',
  green: '\x1b[32m',
  yellow: '\x1b[33m',
  blue: '\x1b[34m',
  cyan: '\x1b[36m'
};

function log(color, prefix, message) {
  console.log(`${color}${prefix}${colors.reset} ${message}`);
}

// Test examples
const TEST_MODULES = {
  Empty: `package examples

import chisel3._

class Empty extends Module {
  val io = IO(new Bundle {
  })
}`,
  
  SimpleAdder: `package examples

import chisel3._

class SimpleAdder extends Module {
  val io = IO(new Bundle {
    val a = Input(UInt(4.W))
    val b = Input(UInt(4.W))
    val sum = Output(UInt(5.W))
  })
  
  io.sum := io.a +& io.b
}`
};

async function testCompilation(moduleName, code, config = {}) {
  const sessionId = Date.now();
  log(colors.blue, '[TEST]', `Testing compilation for module: ${moduleName}`);
  log(colors.cyan, '[INFO]', `Session ID: ${sessionId}`);
  
  try {
    // Step 1: Extract class name
    const classMatch = code.match(/class\s+(\w+)/);
    const actualClassName = classMatch ? classMatch[1] : 'UserModule';
    log(colors.cyan, '[INFO]', `Extracted class name: ${actualClassName}`);
    
    // Step 2: Write file (filename MUST match class name)
    const userFile = path.join(CHISEL_SRC, `${actualClassName}.scala`);
    await fs.writeFile(userFile, code, 'utf-8');
    log(colors.green, '[OK]', `Wrote file: ${userFile}`);
    
    // Step 3: Write config
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
    log(colors.green, '[OK]', `Wrote config: ${JSON.stringify(generationConfig)}`);
    
    // Step 4: Run compilation
    log(colors.yellow, '[COMPILE]', 'Starting SBT compilation...');
    const sbtCommand = `cd ${CHISEL_ROOT} && eval "$(direnv export bash 2>/dev/null)" && make generate MODULE=${actualClassName} V=1`;
    
    try {
      const { stdout, stderr } = await execAsync(sbtCommand, {
        timeout: 120000,
        maxBuffer: 10 * 1024 * 1024,
        shell: '/bin/bash'
      });
      
      log(colors.green, '[OK]', 'Compilation successful!');
      console.log('\n--- SBT Output ---');
      console.log(stdout);
      if (stderr) {
        console.log('\n--- SBT Errors ---');
        console.log(stderr);
      }
    } catch (execError) {
      log(colors.red, '[ERROR]', 'Compilation failed!');
      console.log('\n--- SBT Output ---');
      console.log(execError.stdout || '');
      console.log('\n--- SBT Errors ---');
      console.log(execError.stderr || '');
      throw execError;
    }
    
    // Step 5: Read generated files
    const moduleDir = path.join(CHISEL_GENERATED, actualClassName);
    const verilogPath = path.join(moduleDir, `${actualClassName}.sv`);
    
    try {
      const verilog = await fs.readFile(verilogPath, 'utf-8');
      log(colors.green, '[OK]', `Read generated Verilog: ${verilogPath}`);
      console.log('\n--- Generated SystemVerilog ---');
      console.log(verilog.substring(0, 500) + (verilog.length > 500 ? '\n...(truncated)' : ''));
      return { success: true, verilog };
    } catch (readError) {
      log(colors.red, '[ERROR]', `Could not read Verilog: ${readError.message}`);
      throw readError;
    }
    
  } catch (error) {
    log(colors.red, '[FAIL]', `Test failed: ${error.message}`);
    return { success: false, error: error.message };
  }
}

async function cleanup() {
  try {
    const userFile = path.join(CHISEL_SRC, 'UserModule.scala');
    await fs.unlink(userFile);
    log(colors.yellow, '[CLEANUP]', 'Removed UserModule.scala');
  } catch (e) {
    // Ignore cleanup errors
  }
}

async function main() {
  const args = process.argv.slice(2);
  
  if (args.length === 0) {
    console.log(`${colors.bright}ChiselForge Debug CLI${colors.reset}\n`);
    console.log('Usage:');
    console.log('  node debug-compile.js <module-name>');
    console.log('  node debug-compile.js --list');
    console.log('  node debug-compile.js --all');
    console.log('\nAvailable test modules:');
    Object.keys(TEST_MODULES).forEach(name => {
      console.log(`  - ${name}`);
    });
    process.exit(0);
  }
  
  if (args[0] === '--list') {
    console.log('Available test modules:');
    Object.keys(TEST_MODULES).forEach(name => {
      console.log(`  ${name}`);
    });
    process.exit(0);
  }
  
  if (args[0] === '--all') {
    console.log(`${colors.bright}Testing all modules...${colors.reset}\n`);
    let passed = 0;
    let failed = 0;
    
    for (const [name, code] of Object.entries(TEST_MODULES)) {
      console.log(`\n${'='.repeat(60)}`);
      const result = await testCompilation(name, code);
      await cleanup();
      
      if (result.success) {
        passed++;
      } else {
        failed++;
      }
      console.log(`${'='.repeat(60)}\n`);
    }
    
    console.log(`\n${colors.bright}Summary:${colors.reset}`);
    console.log(`  ${colors.green}Passed: ${passed}${colors.reset}`);
    console.log(`  ${colors.red}Failed: ${failed}${colors.reset}`);
    process.exit(failed > 0 ? 1 : 0);
  }
  
  const moduleName = args[0];
  if (!TEST_MODULES[moduleName]) {
    log(colors.red, '[ERROR]', `Unknown module: ${moduleName}`);
    log(colors.cyan, '[INFO]', `Available modules: ${Object.keys(TEST_MODULES).join(', ')}`);
    process.exit(1);
  }
  
  const result = await testCompilation(moduleName, TEST_MODULES[moduleName]);
  await cleanup();
  
  process.exit(result.success ? 0 : 1);
}

main().catch(err => {
  log(colors.red, '[FATAL]', err.message);
  process.exit(1);
});
