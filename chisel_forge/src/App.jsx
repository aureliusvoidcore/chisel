import React, { useState, useEffect, useRef } from 'react'
import Editor from '@monaco-editor/react'
import { Hammer, Play, Settings, FolderOpen, Save, Download } from 'lucide-react'
import { EXAMPLES } from './examples'
import compilationService from './api'
import EbmcConfig from './components/EbmcConfig'
import BuildConfig from './components/BuildConfig'
import ResizablePanel from './components/ResizablePanel'

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
  
  // Layout state
  const [sidebarWidth, setSidebarWidth] = useState(280);
  const [consoleHeight, setConsoleHeight] = useState(250);
  const [editorSplitPos, setEditorSplitPos] = useState(50); // percentage
  const [activeTab, setActiveTab] = useState('modules'); // 'modules' or 'config'
  
  const [config, setConfig] = useState({
    mode: 'verification',
    layers: 'inline',
    preserve_values: 'named',
    randomization: 'disable',
    run_formal: 'no'
  });

  // Initialize ebmcParams from the default module if available
  const [ebmcParams, setEbmcParams] = useState(EXAMPLES["Empty"]?.ebmcParams || {});

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
    
    // Load EBMC parameters if they exist for this module
    if (EXAMPLES[modName].ebmcParams) {
      setEbmcParams(EXAMPLES[modName].ebmcParams);
      setLogs(prev => [...prev, `[Config] Loaded EBMC parameters for ${modName}`]);
    } else {
      setEbmcParams({});
    }
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

    // Log EBMC parameters being used
    const paramCount = Object.keys(ebmcParams).length;
    if (paramCount > 0) {
      setLogs(prev => [...prev, `[EBMC] Using ${paramCount} parameter(s): ${JSON.stringify(ebmcParams)}`]);
    } else {
      setLogs(prev => [...prev, '[EBMC] Using default parameters']);
    }

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
      <div className="flex-1 flex overflow-hidden">
        {/* Left Sidebar with Tabs (absolute full height) */}
        <div className="bg-neutral-800 border-r border-neutral-700 flex flex-col relative" style={{ width: `${sidebarWidth}px` }}>
            {/* Tab Headers */}
            <div className="flex border-b border-neutral-700 shrink-0">
              <button
                onClick={() => setActiveTab('modules')}
                className={`flex-1 px-4 py-2 text-xs font-semibold uppercase transition-colors ${
                  activeTab === 'modules' 
                    ? 'bg-neutral-900 text-blue-400 border-b-2 border-blue-500' 
                    : 'text-gray-500 hover:text-gray-300 hover:bg-neutral-700'
                }`}
              >
                Modules
              </button>
              <button
                onClick={() => setActiveTab('config')}
                className={`flex-1 px-4 py-2 text-xs font-semibold uppercase transition-colors ${
                  activeTab === 'config' 
                    ? 'bg-neutral-900 text-blue-400 border-b-2 border-blue-500' 
                    : 'text-gray-500 hover:text-gray-300 hover:bg-neutral-700'
                }`}
              >
                Config
              </button>
            </div>

            {/* Tab Content */}
            <div className="flex-1 overflow-hidden">
              {activeTab === 'modules' ? (
                <div className="h-full p-2 overflow-y-auto">
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
              ) : (
                <div className="h-full overflow-y-auto p-4 space-y-3">
                  {/* Verification Status */}
                  <div className={`p-3 rounded-lg text-center text-sm ${
                    verificationResult === 'success' ? 'bg-green-900/20 text-green-400' :
                    verificationResult === 'fail' ? 'bg-red-900/20 text-red-400' :
                    verificationResult === 'error' ? 'bg-yellow-900/20 text-yellow-400' :
                    'bg-neutral-900 text-gray-500'
                  }`}>
                    {verificationResult ? status : 'Ready'}
                  </div>

                  {/* VCD Download */}
                  {vcdFile && (
                    <button
                      onClick={handleDownloadVCD}
                      className="w-full flex items-center justify-center space-x-2 px-3 py-2 bg-green-900/20 hover:bg-green-900/30 text-green-400 rounded text-xs font-medium transition-colors"
                    >
                      <Download className="w-4 h-4" />
                      <span>Download {vcdFile}</span>
                    </button>
                  )}

                  {/* Build Configuration */}
                  <BuildConfig config={config} onChange={setConfig} />

                  {/* EBMC Parameters */}
                  <EbmcConfig config={ebmcParams} onChange={setEbmcParams} />
                </div>
              )}
            </div>

            {/* Resize Handle for Sidebar Width */}
            <div
              onMouseDown={(e) => {
                e.preventDefault();
                const startX = e.clientX;
                const startWidth = sidebarWidth;
                
                const handleMouseMove = (moveEvent) => {
                  const delta = moveEvent.clientX - startX;
                  const newWidth = Math.max(220, Math.min(500, startWidth + delta));
                  setSidebarWidth(newWidth);
                };
                
                const handleMouseUp = () => {
                  document.removeEventListener('mousemove', handleMouseMove);
                  document.removeEventListener('mouseup', handleMouseUp);
                  document.body.style.cursor = '';
                  document.body.style.userSelect = '';
                };
                
                document.addEventListener('mousemove', handleMouseMove);
                document.addEventListener('mouseup', handleMouseUp);
                document.body.style.cursor = 'ew-resize';
                document.body.style.userSelect = 'none';
              }}
              className="absolute top-0 right-0 w-1 h-full cursor-ew-resize hover:bg-blue-500/50 active:bg-blue-500 bg-neutral-700/50 transition-colors z-10"
            />
          </div>

        {/* Right Column: Editors (top) + Console (bottom) */}
        <div className="flex-1 flex flex-col overflow-hidden">
          {/* Editors Row */}
          <div className="flex-1 flex relative overflow-hidden">
          {/* Chisel Editor */}
          <div style={{ width: `${editorSplitPos}%` }} className="bg-neutral-900 flex flex-col">
            <div className="px-3 py-2 bg-neutral-800 border-b border-neutral-700 text-xs font-semibold text-gray-400">
              Chisel Source
            </div>
            <div className="flex-1">
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
                  padding: { top: 10 },
                  scrollBeyondLastLine: false,
                }}
              />
            </div>
          </div>

          {/* Resize Handle */}
          <div
            onMouseDown={(e) => {
              e.preventDefault();
              const container = e.currentTarget.parentElement;
              const containerRect = container.getBoundingClientRect();
              
              const handleMouseMove = (moveEvent) => {
                const offsetX = moveEvent.clientX - containerRect.left;
                const percentage = (offsetX / containerRect.width) * 100;
                const clampedPercentage = Math.max(30, Math.min(70, percentage));
                setEditorSplitPos(clampedPercentage);
              };
              
              const handleMouseUp = () => {
                document.removeEventListener('mousemove', handleMouseMove);
                document.removeEventListener('mouseup', handleMouseUp);
                document.body.style.cursor = '';
                document.body.style.userSelect = '';
              };
              
              document.addEventListener('mousemove', handleMouseMove);
              document.addEventListener('mouseup', handleMouseUp);
              document.body.style.cursor = 'ew-resize';
              document.body.style.userSelect = 'none';
            }}
            className="w-1 cursor-ew-resize hover:bg-blue-500/50 active:bg-blue-500 bg-neutral-700 transition-colors z-50"
          />

          {/* SystemVerilog Viewer */}
          <div style={{ width: `${100 - editorSplitPos}%` }} className="bg-neutral-900 flex flex-col">
            <div className="px-3 py-2 bg-neutral-800 border-b border-neutral-700 text-xs font-semibold text-gray-400">
              Generated SystemVerilog
            </div>
            <div className="flex-1">
              <Editor
                height="100%"
                language="verilog"
                value={verilog}
                theme="vs-dark"
                options={{
                  readOnly: true,
                  minimap: { enabled: true },
                  fontSize: 14,
                  fontFamily: "'JetBrains Mono', 'Fira Code', monospace",
                  padding: { top: 10 },
                  scrollBeyondLastLine: false,
                }}
              />
            </div>
            </div>
          </div>

          {/* Console Row */}
          <div className="flex border-t border-neutral-700" style={{ height: `${consoleHeight}px` }}>
            <div className="flex-1 bg-neutral-950 flex flex-col relative">
            {/* Resize Handle for Console Height */}
            <div
              onMouseDown={(e) => {
                e.preventDefault();
                const startY = e.clientY;
                const startHeight = consoleHeight;
                
                const handleMouseMove = (moveEvent) => {
                  const delta = startY - moveEvent.clientY;
                  const newHeight = Math.max(150, Math.min(600, startHeight + delta));
                  setConsoleHeight(newHeight);
                };
                
                const handleMouseUp = () => {
                  document.removeEventListener('mousemove', handleMouseMove);
                  document.removeEventListener('mouseup', handleMouseUp);
                  document.body.style.cursor = '';
                  document.body.style.userSelect = '';
                };
                
                document.addEventListener('mousemove', handleMouseMove);
                document.addEventListener('mouseup', handleMouseUp);
                document.body.style.cursor = 'ns-resize';
                document.body.style.userSelect = 'none';
              }}
              className="h-1 w-full cursor-ns-resize hover:bg-blue-500/50 active:bg-blue-500 bg-neutral-700 transition-colors"
            />
            
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