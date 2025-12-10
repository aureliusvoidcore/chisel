// Web Worker for Chisel Compilation
// Loads the Scala.js compiled artifact and handles compilation requests

importScripts('/bin/chisel-sandbox-fastopt.js');

self.onmessage = function(e) {
  const { id, type, payload } = e.data;

  if (type === 'elaborate') {
    try {
      const { moduleName, code, config } = payload;
      
      // Call the Scala.js exported function
      // Note: ChiselCompiler is exposed as a global by the imported script
      if (typeof self.ChiselCompiler === 'undefined') {
        throw new Error("ChiselCompiler not loaded. Check chisel-sandbox-fastopt.js");
      }

      // Pass the code to the compiler so it can parse the actual module name
      const firrtl = self.ChiselCompiler.elaborate(moduleName, code);
      
      // We might need to update the module name if the code defines a different one
      // But for now, let's assume the compiler handles the logic of checking the code
      
      const firtoolOpts = self.ChiselCompiler.getFirtoolOptions(moduleName, JSON.stringify(config || {}));
      const verilog = self.ChiselCompiler.generateVerilog(moduleName, code);

      self.postMessage({
        id,
        type: 'success',
        payload: {
          firrtl,
          firtoolOpts,
          verilog
        }
      });
    } catch (err) {
      self.postMessage({
        id,
        type: 'error',
        error: err.message
      });
    }
  } else {
    self.postMessage({
      id,
      type: 'error',
      error: `Unknown message type: ${type}`
    });
  }
};
