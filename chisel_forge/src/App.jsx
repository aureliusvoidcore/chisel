import React, { useState, useEffect, useRef } from 'react'
import Editor from '@monaco-editor/react'
import { Hammer, Play, Settings, FolderOpen, Save, Download } from 'lucide-react'
import { EXAMPLES } from './examples'
import compilationService from './api'
import EbmcConfig from './components/EbmcConfig'

function App() {
  const [code, setCode] = useState(EXAMPLES["Empty"] ? EXAMPLES["Empty"].chisel : "");
  const [verilog, setVerilog] = useState("// Click 'Elaborate' to generate Verilog");
  const [selectedModule, setSelectedModule] = useState("Empty");
  const [moduleName, setModuleName] = useState("Empty");
  const [logs, setLogs] = useState([]);
  const [status, setStatus] = useState("Ready");
  const [isVerifying, setIsVerifying] = useState(false);
  const [isCompiling, setIsCompiling] = useState(false);
  const [verificationResult, setVerificationResult] = useState(null);
  const [backendStatus, setBackendStatus] = useState('checking');
  const [vcdFile, setVcdFile] = useState(null);
  
  const [config, setConfig] = useState({
    mode: 'verification',
    layers: 'inline',
    preserve_values: 'named',
    randomization: 'disable',
    run_formal: 'no'
  });

  const [ebmcParams, setEbmcParams] = useState({});

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

  const handleModuleChange = (modName) => {
    setSelectedModule(modName);
    setModuleName(modName);
    setCode(EXAMPLES[modName].chisel);
    setVerilog("// Click 'Elaborate' to generate Verilog");
    setVerificationResult(null);
    setLogs([]);
    setStatus("Ready");
  };

  const handleCompile = async () => {
    if (backendStatus !== 'connected') {
      setLogs(prev => [...prev, '[Error] Backend server not available']);
      return;
    }

    setIsCompiling(true);
    setStatus("Elaborating...");
    setLogs(prev => [...prev, `Starting elaboration for ${moduleName}`]);
    
    try {
      const result = await compilationService.compile(code, moduleName, config);

      if (result.success) {
        setLogs(prev => [...prev, '[Compiler] ✓ Elaboration successful']);
        if (result.verilog) {
          setVerilog(result.verilog);
          setLogs(prev => [...prev, '[Compiler] ✓ SystemVerilog generated']);
        }
        setStatus('Complete');
      } else {
        setLogs(prev => [...prev, `[Error] ${result.error}`]);
        if (result.stderr) setLogs(prev => [...prev, result.stderr]);
        setStatus('Failed');
      }
    } catch (error) {
      setLogs(prev => [...prev, `[Error] ${error.message}`]);
      setStatus('Failed');
    } finally {
      setIsCompiling(false);
    }
  };

  const handleVerify = async () => {
    if (!moduleName) {
      setLogs(['Error: Please specify a module name']);
      return;
    }
    
    setLogs([`Compiling ${moduleName}...`]);
    setStatus("Compiling...");
    
    try {
      const compileResult = await compilationService.compile(code, moduleName, config);
      
      if (!compileResult.success) {
        setLogs(prev => [...prev, `[Error] ${compileResult.error}`]);
        setStatus('Failed');
        return;
      }
      
      setLogs(prev => [...prev, '[Compiler] ✓ Compiled, verifying...']);
      if (compileResult.verilog) setVerilog(compileResult.verilog);
    } catch (error) {
      setLogs(prev => [...prev, `[Error] ${error.message}`]);
      setStatus('Failed');
      return;
    }
    
    setIsVerifying(true);
    setStatus("Verifying...");
    setVerificationResult(null);
    setVcdFile(null);

    try {
        const response = await compilationService.verify(moduleName, ebmcParams);
        
        if (response.success) {
            const { results, stdout, vcdFile: generatedVcd } = response;
            if (generatedVcd) {
                setVcdFile(generatedVcd);
                setLogs(prev => [...prev, `✓ VCD file generated: ${generatedVcd}`]);
            }
            const proved = results.proved || [];
            const failed = results.failed || [];
            
            setLogs([
                `Verification completed for ${moduleName}`,
                `Mode: ${response.mode}`,
                '',
                `✓ Proved: ${proved.length} properties`,
                `✗ Failed: ${failed.length} properties`,
                '',
                ...stdout.split('\n')
            ]);
            
            if (failed.length > 0) {
                setVerificationResult('fail');
                setStatus(`Failed - ${failed.length} properties refuted`);
            } else if (proved.length > 0) {
                setVerificationResult('success');
                setStatus(`Success - ${proved.length} properties proved`);
            } else {
                setVerificationResult('unknown');
                setStatus("Complete");
            }
        } else {
            setLogs([`Error: ${response.error}`, '', response.stdout || '']);
            setVerificationResult('error');
            setStatus("Error");
        }
    } catch (e) {
        setLogs(prev => [...prev, `Error: ${e.message}`]);
        setStatus("Error");
        setVerificationResult('error');
    } finally {
        setIsVerifying(false);
    }
  };

  const handleDownloadVCD = async () => {
    if (!vcdFile || !moduleName) return;
    
    try {
      setLogs(prev => [...prev, `Downloading ${vcdFile}...`]);
      const blob = await compilationService.downloadVCD(moduleName, vcdFile);
      
      // Create download link
      const url = window.URL.createObjectURL(blob);
      const a = document.createElement('a');
      a.href = url;
      a.download = vcdFile;
      document.body.appendChild(a);
      a.click();
      document.body.removeChild(a);
      window.URL.revokeObjectURL(url);
      
      setLogs(prev => [...prev, `✓ Downloaded ${vcdFile}`]);
    } catch (error) {
      setLogs(prev => [...prev, `✗ Download failed: ${error.message}`]);
    }
  };

  return (
    <div className="flex flex-col h-screen w-screen bg-neutral-900 text-gray-200 font-sans overflow-hidden">
      {/* Header */}
      <header className="h-14 bg-neutral-800 border-b border-neutral-700 flex items-center px-4 justify-between shadow-md shrink-0">
        <div className="flex items-center space-x-3">
          <div className="bg-blue-600 p-1.5 rounded-lg">
            <Hammer className="w-5 h-5 text-white" />
          </div>
          <span className="font-bold text-xl text-gray-100">ChiselForge</span>
        </div>
        <div className="flex items-center space-x-4">
          <div className="flex items-center space-x-2">
            <label className="text-xs text-gray-400">Module:</label>
            <input 
              type="text"
              value={moduleName}
              onChange={(e) => setModuleName(e.target.value)}
              placeholder="ModuleName"
              className="px-3 py-1.5 bg-neutral-700 border border-neutral-600 rounded text-sm text-gray-200 focus:outline-none focus:border-blue-500"
            />
          </div>
          <button className="p-2 hover:bg-neutral-700 rounded-md transition-colors text-gray-400 hover:text-white">
            <FolderOpen className="w-5 h-5" />
          </button>
          <button className="p-2 hover:bg-neutral-700 rounded-md transition-colors text-gray-400 hover:text-white">
            <Save className="w-5 h-5" />
          </button>
          <div className="h-6 w-px bg-neutral-600 mx-2"></div>
          <button 
            onClick={handleCompile}
            disabled={isCompiling || isVerifying}
            className={`flex items-center space-x-2 px-4 py-2 rounded-lg transition-all shadow-lg ${
                isCompiling ? 'bg-purple-800 cursor-wait' : 'bg-purple-600 hover:bg-purple-500'
            } text-white font-medium disabled:opacity-50`}
          >
            <Settings className={`w-4 h-4 ${isCompiling ? 'animate-spin' : ''}`} />
            <span>Elaborate</span>
          </button>
          <button 
            onClick={handleVerify}
            disabled={isVerifying || isCompiling}
            className={`flex items-center space-x-2 px-4 py-2 rounded-lg transition-all shadow-lg ${
                isVerifying ? 'bg-blue-800 cursor-wait' : 'bg-blue-600 hover:bg-blue-500'
            } text-white font-medium disabled:opacity-50`}
          >
            <Play className={`w-4 h-4 ${isVerifying ? 'animate-spin' : ''}`} />
            <span>Verify</span>
          </button>
        </div>
      </header>

      {/* Main Content Area */}
      <div className="flex-1 flex flex-col overflow-hidden">
        {/* Top Row: Sidebar + Editor (Full Width) */}
        <div className="flex-1 flex overflow-hidden">
          {/* Sidebar */}
          <aside className="w-56 bg-neutral-800 border-r border-neutral-700 flex flex-col">
            <div className="p-3 border-b border-neutral-700 text-xs uppercase font-semibold text-gray-500">
              Modules
            </div>
            <div className="flex-1 p-2 overflow-y-auto">
              {Object.keys(EXAMPLES).map(mod => (
                <div 
                  key={mod}
                  onClick={() => handleModuleChange(mod)}
                  className={`px-3 py-2 rounded cursor-pointer text-sm flex items-center space-x-2 ${
                    selectedModule === mod ? 'bg-blue-900/30 text-blue-400 border border-blue-800/50' : 'text-gray-400 hover:bg-neutral-700'
                  }`}
                >
                  <span className="w-2 h-2 rounded-full bg-orange-500"></span>
                  <span>{mod}.scala</span>
                </div>
              ))}
            </div>
          </aside>

          {/* Editor - Takes Full Width */}
          <main className="flex-1 bg-neutral-900">
            <Editor
              height="100%"
              language="scala"
              value={code}
              onChange={(val) => setCode(val)}
              theme="vs-dark"
              options={{
                minimap: { enabled: true },
                fontSize: 14,
                fontFamily: "'JetBrains Mono', 'Fira Code', monospace",
                padding: { top: 20 },
                scrollBeyondLastLine: false,
              }}
            />
          </main>
        </div>

        {/* Bottom Row: Console + Config Panel */}
        <div className="h-60 flex border-t border-neutral-700">
          {/* Console Output - 70% width */}
          <div className="flex-[7] bg-neutral-950 border-r border-neutral-700 flex flex-col">
            <div className="flex items-center justify-between px-4 py-2 bg-neutral-900 border-b border-neutral-800">
              <span className="text-xs font-semibold text-gray-400 uppercase tracking-wider">Console</span>
              <button 
                onClick={() => setLogs([])} 
                className="text-xs text-gray-500 hover:text-gray-300 px-2 py-1 rounded hover:bg-neutral-800"
              >
                Clear
              </button>
            </div>
            <div className="flex-1 overflow-y-auto p-3 font-mono text-xs space-y-0.5">
              {logs.length === 0 ? (
                <div className="text-gray-600 italic">Console output will appear here...</div>
              ) : (
                logs.map((line, i) => (
                  <div key={i} className={`leading-relaxed ${
                      line.includes("✓") || line.includes("success") ? "text-green-400" :
                      line.includes("✗") || line.includes("Error") || line.includes("error") ? "text-red-400" :
                      line.includes("Warning") || line.includes("warning") ? "text-yellow-400" :
                      line.includes("[") ? "text-blue-400" : "text-gray-300"
                  }`}>
                    {line}
                  </div>
                ))
              )}
            </div>
          </div>

          {/* Right Panel: Status + Config - 30% width */}
          <div className="flex-[3] bg-neutral-800 flex flex-col">
            <div className="px-4 py-2 border-b border-neutral-700 bg-neutral-900">
              <span className="text-xs font-semibold text-gray-400 uppercase tracking-wider">Status & Configuration</span>
            </div>
            
            <div className="flex-1 overflow-y-auto p-4 space-y-4">
              {/* Verification Status */}
              <div className={`p-4 rounded-lg text-center text-sm ${
                verificationResult === 'success' ? 'bg-green-900/20 text-green-400' :
                verificationResult === 'fail' ? 'bg-red-900/20 text-red-400' :
                verificationResult === 'error' ? 'bg-yellow-900/20 text-yellow-400' :
                'bg-neutral-900 text-gray-500'
              }`}>
                {verificationResult ? status : 'Ready'}
              </div>

              {/* Config Options */}
              <div className="space-y-4">
                {/* EBMC Parameters */}
                <EbmcConfig config={ebmcParams} onChange={setEbmcParams} />

                {/* VCD Download Button */}
                {vcdFile && (
                  <button
                    onClick={handleDownloadVCD}
                    className="w-full flex items-center justify-center space-x-2 px-3 py-2 bg-green-900/20 hover:bg-green-900/30 text-green-400 rounded text-xs font-medium transition-colors"
                  >
                    <Download className="w-4 h-4" />
                    <span>Download {vcdFile}</span>
                  </button>
                )}

                <div className="border-t border-neutral-700 pt-3">
                  <div className="text-xs font-semibold text-gray-400 uppercase tracking-wide mb-2">Elaboration Config</div>
                </div>

                <div>
                  <label className="text-xs text-gray-400 block mb-1">Mode</label>
                  <select 
                    value={config.mode}
                    onChange={(e) => setConfig({...config, mode: e.target.value})}
                    className="w-full bg-neutral-700 border border-neutral-600 rounded px-2 py-1.5 text-xs text-gray-200"
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
                    className="w-full bg-neutral-700 border border-neutral-600 rounded px-2 py-1.5 text-xs text-gray-200"
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
                    className="w-full bg-neutral-700 border border-neutral-600 rounded px-2 py-1.5 text-xs text-gray-200"
                  >
                    <option value="named">Named</option>
                    <option value="all">All</option>
                    <option value="none">None</option>
                  </select>
                </div>
              </div>

              {/* Generated Verilog Preview */}
              <div>
                <div className="text-xs font-semibold text-blue-400 mb-2">Generated SystemVerilog</div>
                <div className="bg-neutral-900 rounded border border-neutral-700 p-2 font-mono text-xs text-gray-400 overflow-auto max-h-48">
                  <pre className="whitespace-pre-wrap">{verilog}</pre>
                </div>
              </div>
            </div>
          </div>
        </div>
      </div>

      {/* Status Bar */}
      <footer className="h-7 bg-blue-950 text-blue-200/80 text-xs flex items-center px-3 justify-between border-t border-blue-900">
        <div className="flex items-center space-x-4">
            <span>Chisel 7.4.0</span>
            <span>Scala 2.13.14</span>
            <span>EBMC</span>
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
            <div className={`w-2 h-2 rounded-full ${isVerifying || isCompiling ? 'bg-yellow-400 animate-pulse' : 'bg-green-400'}`}></div>
            <span>{status}</span>
        </div>
      </footer>
    </div>
  )
}

export default App
