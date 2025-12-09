import React, { useState, useEffect, useRef } from 'react'
import Editor from '@monaco-editor/react'
import { Hammer, Play, Settings, Moon, Sun, HelpCircle, Share2, FolderOpen, Save, CheckCircle, XCircle, AlertTriangle } from 'lucide-react'
import { EXAMPLES } from './examples'
import compilationService from './api'

function App() {
  const [code, setCode] = useState(EXAMPLES["Empty"] ? EXAMPLES["Empty"].chisel : "");
  const [verilog, setVerilog] = useState("// Click 'Elaborate' to generate Verilog");
  const [selectedModule, setSelectedModule] = useState("Empty");
  const [moduleName, setModuleName] = useState("Empty"); // User-specified module name
  const [logs, setLogs] = useState([]);
  const [status, setStatus] = useState("Ready");
  const [isVerifying, setIsVerifying] = useState(false);
  const [verificationResult, setVerificationResult] = useState(null); // 'success', 'fail', 'error'
  const [activeTab, setActiveTab] = useState('verification'); // 'verification' or 'config'
  
  // Configuration state
  const [config, setConfig] = useState({
    mode: 'verification',
    layers: 'inline',
    preserve_values: 'named',
    randomization: 'disable',
    run_formal: 'no'
  });
  
  const [firtoolConfig, setFirtoolConfig] = useState(`--verification-flavor=sva
--split-verilog
--lowering-options=disallowLocalVariables,disallowMuxInlining,disallowExpressionInliningInPorts,disallowPackedArrays,noAlwaysComb,verifLabels
--no-dedup
--preserve-values=named
--disable-all-randomization
--strip-debug-info`);
  
  const hwcbmcRef = useRef(null);

  useEffect(() => {
    // Load the HWCBMC script dynamically
    const script = document.createElement('script');
    script.src = "./bin/hwcbmc.js";
    script.async = true;
    script.onload = () => {
      console.log("HWCBMC script loaded");
      // Load the wrapper
      fetch('./bin/hwcbmc-wrapper.js')
        .then(res => res.text())
        .then(text => {
            // Quick hack to make the class available
            const cleanText = text.replace('export default', '');
            // eslint-disable-next-line no-eval
            eval(cleanText); 
            // Now HWCBMCWrapper should be available globally if defined as class
            // Or we can just paste the wrapper code here for safety.
        });
    };
    document.body.appendChild(script);

    return () => {
      document.body.removeChild(script);
    }
  }, []);

  // Initialize HWCBMC Wrapper manually for now since the import might be tricky with mixed module types
  const initWrapper = async () => {
    if (hwcbmcRef.current) return hwcbmcRef.current;

    // Define the wrapper class inline if needed or ensure it's loaded
    if (typeof window.HWCBMCWrapper === 'undefined') {
        // Simple inline definition based on the file we read
        window.HWCBMCWrapper = class HWCBMCWrapper {
            constructor() {
                this.module = null;
                this.ready = false;
                this.outputBuffer = [];
                this.errorBuffer = [];
            }
        
            async initialize(overrides = {}) {
                if (this.ready) return;
        
                const baseConfig = {
                    print: (t) => {
                        console.log('[EBMC]', t);
                        this.outputBuffer.push(t);
                    },
                    printErr: (t) => {
                        console.error('[EBMC Err]', t);
                        this.errorBuffer.push(t);
                    },
                    noInitialRun: true,
                    locateFile: (path, prefix) => {
                        if (path.endsWith('.wasm')) {
                            return './bin/' + path;
                        }
                        return prefix + path;
                    }
                };
        
                const cfg = { ...baseConfig, ...overrides };
        
                if (typeof window.HWCBMCModule === 'undefined') {
                    throw new Error('HWCBMCModule factory not found. Make sure hwcbmc.js is loaded.');
                }
        
                this.module = await window.HWCBMCModule(cfg);
                this.ready = true;
            }
        
            writeFile(name, content) {
                if (!this.ready) throw new Error('HW-CBMC module not initialized');
                this.module.FS.writeFile(name, content);
            }

            run(args) {
                if (!this.ready) throw new Error('HW-CBMC module not initialized');
                this.outputBuffer = [];
                this.errorBuffer = [];
                try {
                    this.module.callMain(args);
                    return { exitCode: 0, stdout: this.outputBuffer.join('\n'), stderr: this.errorBuffer.join('\n') };
                } catch (e) {
                    // Emscripten might throw on exit
                    if (e.status !== undefined) {
                         return { exitCode: e.status, stdout: this.outputBuffer.join('\n'), stderr: this.errorBuffer.join('\n') };
                    }
                    throw e;
                }
            }
        };
    }

    const wrapper = new window.HWCBMCWrapper();
    // If the wrapper was loaded from file (which lacks run()), we need to patch it or use our inline one.
    // The issue is that if window.HWCBMCWrapper is already defined by the eval/script, it might be the incomplete one.
    // Let's force patch the run method if it's missing.
    if (!wrapper.run) {
        wrapper.run = function(args) {
            if (!this.ready) throw new Error('HW-CBMC module not initialized');
            this.outputBuffer = [];
            this.errorBuffer = [];
            try {
                this.module.callMain(args);
                return { exitCode: 0, stdout: this.outputBuffer.join('\n'), stderr: this.errorBuffer.join('\n') };
            } catch (e) {
                // Emscripten might throw on exit
                if (e.status !== undefined) {
                        return { exitCode: e.status, stdout: this.outputBuffer.join('\n'), stderr: this.errorBuffer.join('\n') };
                }
                throw e;
            }
        };
    }

    await wrapper.initialize();
    hwcbmcRef.current = wrapper;
    return wrapper;
  };

  const handleModuleChange = (modName) => {
    setSelectedModule(modName);
    setModuleName(modName);
    setCode(EXAMPLES[modName].chisel);
    setVerilog("// Click 'Elaborate' to generate Verilog");
    setVerificationResult(null);
    setLogs([]);
    setStatus("Ready");
  };

  const [isCompiling, setIsCompiling] = useState(false);
  const [backendStatus, setBackendStatus] = useState('checking');

  // Check backend health on mount
  useEffect(() => {
    const checkBackend = async () => {
      try {
        await compilationService.health();
        setBackendStatus('connected');
        setLogs(prev => [...prev, '[Backend] Connected to compilation server']);
      } catch (error) {
        setBackendStatus('disconnected');
        setLogs(prev => [...prev, `[Backend] Warning: Compilation server offline - ${error.message}`]);
      }
    };
    checkBackend();
  }, []);

  const handleCompile = async () => {
    if (backendStatus !== 'connected') {
      setLogs(prev => [...prev, '[Error] Backend server not available. Please start the compilation server.']);
      return;
    }

    setIsCompiling(true);
    setStatus("Elaborating Chisel...");
    setLogs(prev => [...prev, `Starting elaboration for module: ${moduleName}`]);
    
    try {
      const result = await compilationService.compile(code, moduleName, config);

      if (result.success) {
        setLogs(prev => [...prev, '[Compiler] Elaboration successful']);
        setLogs(prev => [...prev, `[Compiler] Module: ${moduleName}`]);
        
        if (result.verilog) {
          setVerilog(result.verilog);
          setLogs(prev => [...prev, '[Compiler] SystemVerilog generated successfully']);
        }

        if (result.firrtl) {
          console.log('[FIRRTL Output]:\n', result.firrtl);
        }

        if (result.stdout) {
          console.log('[SBT Output]:\n', result.stdout);
        }

        setStatus('Elaboration Complete');
      } else {
        setLogs(prev => [...prev, `[Compiler Error] ${result.error}`]);
        if (result.errors && result.errors.length > 0) {
          result.errors.forEach(err => {
            setLogs(prev => [...prev, `  ${err.message}`]);
          });
        }
        if (result.stderr) {
          setLogs(prev => [...prev, `[Details] ${result.stderr}`]);
        }
        setStatus('Compilation Failed');
      }
    } catch (error) {
      setLogs(prev => [...prev, `[Error] ${error.message}`]);
      setStatus('Compilation Failed');
    } finally {
      setIsCompiling(false);
    }
  };

  const handleVerify = async () => {
    if (!moduleName || moduleName.trim() === '') {
      setLogs(['Error: Please specify a module name.']);
      setStatus('No Module Name');
      return;
    }
    
    // First compile, then verify
    setLogs([`Compiling module ${moduleName}...`]);
    setStatus("Compiling before verification...");
    
    try {
      const compileResult = await compilationService.compile(code, moduleName, config);
      
      if (!compileResult.success) {
        setLogs(prev => [...prev, `[Compilation Error] ${compileResult.error}`]);
        setStatus('Compilation Failed');
        return;
      }
      
      setLogs(prev => [...prev, '[Compiler] Compilation successful, proceeding to verification...']);
      
      if (compileResult.verilog) {
        setVerilog(compileResult.verilog);
      }
    } catch (error) {
      setLogs(prev => [...prev, `[Error] ${error.message}`]);
      setStatus('Compilation Failed');
      return;
    }
    
    setIsVerifying(true);
    setStatus("Running formal verification...");
    setVerificationResult(null);

    try {
        // Use the backend API to run EBMC on the compiled module
        const response = await compilationService.verify(moduleName);
        
        if (response.success) {
            const { results, stdout } = response;
            
            // Parse the results
            const proved = results.proved || [];
            const failed = results.failed || [];
            const unsupported = results.unsupported || [];
            const inconclusive = results.inconclusive || [];
            
            setLogs([
                `Verification completed for ${moduleName}`,
                `Mode: ${response.mode}`,
                '',
                `✓ Proved: ${proved.length} properties`,
                `✗ Failed: ${failed.length} properties`,
                `? Unsupported: ${unsupported.length} properties`,
                `~ Inconclusive: ${inconclusive.length} properties`,
                '',
                ...stdout.split('\n')
            ]);
            
            if (failed.length > 0) {
                setVerificationResult('fail');
                setStatus(`Verification Failed - ${failed.length} properties refuted`);
            } else if (proved.length > 0) {
                setVerificationResult('success');
                setStatus(`Verification Successful - ${proved.length} properties proved`);
            } else {
                setVerificationResult('unknown');
                setStatus("Verification Complete (Check Logs)");
            }
        } else {
            setLogs([`Error: ${response.error}`, '', response.stdout || '']);
            setVerificationResult('error');
            setStatus("Verification Error");
        }

    } catch (e) {
        console.error(e);
        setLogs(prev => [...prev, `Error: ${e.message}`]);
        setStatus("Error during verification");
        setVerificationResult('error');
    } finally {
        setIsVerifying(false);
    }
  };

  return (
    <div className="flex flex-col h-screen bg-neutral-900 text-gray-200 font-sans">
      {/* Top Bar */}
      <header className="h-14 bg-neutral-800 border-b border-neutral-700 flex items-center px-4 justify-between shadow-md z-10">
        <div className="flex items-center space-x-3">
          <div className="bg-blue-600 p-1.5 rounded-lg">
            <Hammer className="w-5 h-5 text-white" />
          </div>
          <span className="font-bold text-xl tracking-tight text-gray-100">ChiselForge</span>
        </div>
        <div className="flex items-center space-x-4">
          <div className="flex items-center space-x-2">
            <label className="text-xs text-gray-400">Module:</label>
            <input 
              type="text"
              value={moduleName}
              onChange={(e) => setModuleName(e.target.value)}
              placeholder="ModuleName"
              className="px-3 py-1.5 bg-neutral-700 border border-neutral-600 rounded text-sm text-gray-200 focus:outline-none focus:border-blue-500 focus:ring-1 focus:ring-blue-500"
            />
          </div>
          <button className="p-2 hover:bg-neutral-700 rounded-md transition-colors text-gray-400 hover:text-white"><FolderOpen className="w-5 h-5" /></button>
          <button className="p-2 hover:bg-neutral-700 rounded-md transition-colors text-gray-400 hover:text-white"><Save className="w-5 h-5" /></button>
          <div className="h-6 w-px bg-neutral-600 mx-2"></div>
          <button 
            onClick={handleCompile}
            disabled={isCompiling || isVerifying}
            className={`flex items-center space-x-2 px-4 py-2 rounded-full transition-all shadow-lg ${
                isCompiling ? 'bg-purple-800 cursor-wait' : 'bg-purple-600 hover:bg-purple-500 hover:scale-105'
            } text-white font-medium`}
          >
            <Settings className={`w-4 h-4 ${isCompiling ? 'animate-spin' : ''}`} />
            <span>{isCompiling ? 'Elaborate' : 'Elaborate'}</span>
          </button>
          <button 
            onClick={handleVerify}
            disabled={isVerifying}
            className={`flex items-center space-x-2 px-4 py-2 rounded-full transition-all shadow-lg ${
                isVerifying ? 'bg-blue-800 cursor-wait' : 'bg-blue-600 hover:bg-blue-500 hover:scale-105'
            } text-white font-medium`}
          >
            <Play className={`w-4 h-4 ${isVerifying ? 'animate-spin' : 'fill-current'}`} />
            <span>{isVerifying ? 'Verifying...' : 'Verify'}</span>
          </button>
          <div className="h-6 w-px bg-neutral-600 mx-2"></div>
          <button className="p-2 hover:bg-neutral-700 rounded-md transition-colors text-gray-400 hover:text-white"><Settings className="w-5 h-5" /></button>
        </div>
      </header>

      {/* Main Content */}
      <div className="flex-1 flex overflow-hidden">
        {/* Sidebar */}
        <aside className="w-64 bg-neutral-800 border-r border-neutral-700 flex flex-col shadow-inner">
          <div className="p-3 border-b border-neutral-700 font-semibold text-xs uppercase tracking-wider text-gray-500">Project Explorer</div>
          <div className="flex-1 p-2 overflow-y-auto">
            <div className="mb-4">
                <div className="text-xs font-semibold text-gray-500 mb-2 px-2">MODULES</div>
                {Object.keys(EXAMPLES).map(mod => (
                    <div 
                        key={mod}
                        onClick={() => handleModuleChange(mod)}
                        className={`px-3 py-2 rounded cursor-pointer text-sm flex items-center space-x-2 ${selectedModule === mod ? 'bg-blue-900/30 text-blue-400 border border-blue-800/50' : 'text-gray-400 hover:bg-neutral-700'}`}
                    >
                        <span className="w-2 h-2 rounded-full bg-orange-500"></span>
                        <span>{mod}.scala</span>
                    </div>
                ))}
            </div>
          </div>
          <div className="p-4 border-t border-neutral-700 bg-neutral-800/50">
            <div className="font-semibold text-xs uppercase tracking-wider text-gray-500 mb-3">Configuration</div>
            <div className="space-y-2">
                <div className="flex justify-between text-xs">
                    <span className="text-gray-400">Engine</span>
                    <span className="text-blue-300">EBMC (Wasm)</span>
                </div>
                <div className="flex justify-between text-xs">
                    <span className="text-gray-400">Bound</span>
                    <span className="text-gray-200">20</span>
                </div>
            </div>
          </div>
        </aside>

        {/* Editor Pane */}
        <main className="flex-1 flex flex-col bg-neutral-900 relative">
          <div className="flex-1 relative">
            <Editor
              height="100%"
              language="scala"
              value={code}
              onChange={(val) => setCode(val)}
              theme="vs-dark"
              options={{
                minimap: { enabled: false },
                fontSize: 14,
                fontFamily: "'JetBrains Mono', 'Fira Code', monospace",
                padding: { top: 20 },
                scrollBeyondLastLine: false,
              }}
            />
          </div>
          {/* Mini-pane for FIRRTL/Verilog preview */}
          <div className="h-40 border-t border-neutral-700 bg-neutral-950 flex flex-col">
             <div className="px-4 py-1 bg-neutral-900 border-b border-neutral-800 text-xs font-mono text-gray-500 flex justify-between">
                <span>GENERATED SYSTEMVERILOG</span>
                <span>Read-only</span>
             </div>
             <div className="flex-1 p-4 font-mono text-xs text-gray-400 overflow-auto whitespace-pre">
                {verilog}
             </div>
          </div>
        </main>

        {/* Right Analysis Pane */}
        <aside className="w-96 bg-neutral-800 border-l border-neutral-700 flex flex-col shadow-xl z-10">
          <div className="flex border-b border-neutral-700 bg-neutral-800">
            <button 
              onClick={() => setActiveTab('verification')}
              className={`flex-1 py-3 text-sm font-medium transition-colors ${
                activeTab === 'verification' 
                  ? 'border-b-2 border-blue-500 text-white bg-neutral-700/50' 
                  : 'text-gray-400 hover:bg-neutral-700 hover:text-gray-200'
              }`}
            >
              Verification
            </button>
            <button 
              onClick={() => setActiveTab('config')}
              className={`flex-1 py-3 text-sm font-medium transition-colors ${
                activeTab === 'config' 
                  ? 'border-b-2 border-blue-500 text-white bg-neutral-700/50' 
                  : 'text-gray-400 hover:bg-neutral-700 hover:text-gray-200'
              }`}
            >
              Configuration
            </button>
          </div>
          
          {activeTab === 'verification' && (
            <div className="flex-1 flex flex-col overflow-hidden">
              {/* Status Header */}
              <div className={`p-6 text-center border-b border-neutral-700 ${
                  verificationResult === 'success' ? 'bg-green-900/20' : 
                  verificationResult === 'fail' ? 'bg-red-900/20' : 'bg-neutral-800'
              }`}>
                  {verificationResult === 'success' && (
                      <div className="flex flex-col items-center text-green-400">
                          <CheckCircle className="w-12 h-12 mb-2" />
                          <span className="text-lg font-bold">Property Proved</span>
                      </div>
                  )}
                  {verificationResult === 'fail' && (
                      <div className="flex flex-col items-center text-red-400">
                          <XCircle className="w-12 h-12 mb-2" />
                          <span className="text-lg font-bold">Property Falsified</span>
                      </div>
                  )}
                  {verificationResult === 'error' && (
                      <div className="flex flex-col items-center text-yellow-400">
                          <AlertTriangle className="w-12 h-12 mb-2" />
                          <span className="text-lg font-bold">Error</span>
                      </div>
                  )}
                  {!verificationResult && (
                      <div className="text-gray-500 py-4">
                          Ready to verify
                      </div>
                  )}
              </div>

              {/* Logs */}
              <div className="flex-1 overflow-y-auto p-4 font-mono text-xs space-y-1 bg-neutral-900 text-gray-300">
                  {logs.length === 0 ? (
                      <span className="text-gray-600 italic">Console output will appear here...</span>
                  ) : (
                      logs.map((line, i) => (
                          <div key={i} className={`${
                              line.includes("SUCCESSFUL") ? "text-green-400 font-bold" :
                              line.includes("FAILED") ? "text-red-400 font-bold" :
                              line.includes("Error") ? "text-yellow-400" : ""
                          }`}>
                              {line}
                          </div>
                      ))
                  )}
              </div>
            </div>
          )}
          
          {activeTab === 'config' && (
            <div className="flex-1 overflow-y-auto p-4 bg-neutral-900 space-y-6">
              {/* Generation Config */}
              <div>
                <h3 className="text-sm font-bold text-blue-400 mb-3 flex items-center">
                  <Settings className="w-4 h-4 mr-2" />
                  Generation Configuration
                </h3>
                <div className="space-y-3">
                  <div>
                    <label className="text-xs text-gray-400 block mb-1">Mode</label>
                    <select 
                      value={config.mode}
                      onChange={(e) => setConfig({...config, mode: e.target.value})}
                      className="w-full bg-neutral-800 border border-neutral-600 rounded px-3 py-2 text-sm text-gray-200 focus:border-blue-500 focus:outline-none"
                    >
                      <option value="verification">Verification</option>
                      <option value="synthesis">Synthesis</option>
                    </select>
                  </div>
                  
                  <div>
                    <label className="text-xs text-gray-400 block mb-1">Layers</label>
                    <select 
                      value={config.layers}
                      onChange={(e) => setConfig({...config, layers: e.target.value})}
                      className="w-full bg-neutral-800 border border-neutral-600 rounded px-3 py-2 text-sm text-gray-200 focus:border-blue-500 focus:outline-none"
                    >
                      <option value="inline">Inline</option>
                      <option value="split">Split (bind)</option>
                    </select>
                  </div>
                  
                  <div>
                    <label className="text-xs text-gray-400 block mb-1">Preserve Values</label>
                    <select 
                      value={config.preserve_values}
                      onChange={(e) => setConfig({...config, preserve_values: e.target.value})}
                      className="w-full bg-neutral-800 border border-neutral-600 rounded px-3 py-2 text-sm text-gray-200 focus:border-blue-500 focus:outline-none"
                    >
                      <option value="named">Named</option>
                      <option value="all">All</option>
                      <option value="none">None</option>
                    </select>
                  </div>
                  
                  <div>
                    <label className="text-xs text-gray-400 block mb-1">Randomization</label>
                    <select 
                      value={config.randomization}
                      onChange={(e) => setConfig({...config, randomization: e.target.value})}
                      className="w-full bg-neutral-800 border border-neutral-600 rounded px-3 py-2 text-sm text-gray-200 focus:border-blue-500 focus:outline-none"
                    >
                      <option value="disable">Disable</option>
                      <option value="enable">Enable</option>
                    </select>
                  </div>
                  
                  <div>
                    <label className="text-xs text-gray-400 block mb-1">Run Formal</label>
                    <select 
                      value={config.run_formal}
                      onChange={(e) => setConfig({...config, run_formal: e.target.value})}
                      className="w-full bg-neutral-800 border border-neutral-600 rounded px-3 py-2 text-sm text-gray-200 focus:border-blue-500 focus:outline-none"
                    >
                      <option value="no">No</option>
                      <option value="default">Default</option>
                      <option value="k-induction">K-Induction</option>
                      <option value="ic3">IC3</option>
                    </select>
                  </div>
                </div>
              </div>
              
              {/* Firtool Config */}
              <div>
                <h3 className="text-sm font-bold text-blue-400 mb-3">Firtool Options</h3>
                <textarea
                  value={firtoolConfig}
                  onChange={(e) => setFirtoolConfig(e.target.value)}
                  className="w-full h-48 bg-neutral-800 border border-neutral-600 rounded px-3 py-2 text-xs font-mono text-gray-200 focus:border-blue-500 focus:outline-none resize-none"
                  placeholder="Enter firtool command-line options (one per line)"
                />
                <p className="text-xs text-gray-500 mt-2">
                  These options are passed to CIRCT's firtool for FIRRTL → SystemVerilog conversion
                </p>
              </div>
              
              {/* Build Info */}
              <div>
                <h3 className="text-sm font-bold text-blue-400 mb-3">Build System Info</h3>
                <div className="bg-neutral-800 rounded p-3 text-xs font-mono space-y-1 text-gray-300">
                  <div><span className="text-gray-500">Command:</span> make generate MODULE=YourModule</div>
                  <div><span className="text-gray-500">SBT:</span> tools/sbt/bin/sbt</div>
                  <div><span className="text-gray-500">Chisel:</span> 7.4.0</div>
                  <div><span className="text-gray-500">Scala:</span> 2.13.14</div>
                  <div><span className="text-gray-500">CIRCT:</span> firtool 1.137.0</div>
                </div>
              </div>
            </div>
          )}
        </aside>
      </div>

      {/* Status Bar */}
      <footer className="h-7 bg-blue-950 text-blue-200/80 text-xs flex items-center px-3 justify-between border-t border-blue-900">
        <div className="flex items-center space-x-4">
            <span>Chisel 7.4.0</span>
            <span>Scala 2.13.14</span>
            <span>EBMC Wasm</span>
            <span className={`flex items-center space-x-1 ${
              backendStatus === 'connected' ? 'text-green-400' : 
              backendStatus === 'disconnected' ? 'text-red-400' : 'text-yellow-400'
            }`}>
              <div className={`w-2 h-2 rounded-full ${
                backendStatus === 'connected' ? 'bg-green-400' : 
                backendStatus === 'disconnected' ? 'bg-red-400' : 'bg-yellow-400 animate-pulse'
              }`}></div>
              <span>Backend: {backendStatus}</span>
            </span>
        </div>
        <div className="flex items-center space-x-2">
            <div className={`w-2 h-2 rounded-full ${isVerifying ? 'bg-yellow-400 animate-pulse' : 'bg-green-400'}`}></div>
            <span>{status}</span>
        </div>
      </footer>
    </div>
  )
}

export default App
