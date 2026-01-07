
import compilationService from './api';

async function runDebugFlow() {
    const log = (msg) => {
        console.log(`[Debug] ${msg}`);
        const el = document.getElementById('debug-log');
        if (el) el.innerText += msg + '\n';
    };

    log("Starting debug flow...");

    // 1. Health Check
    try {
        const health = await compilationService.health();
        log(`Health check: ${JSON.stringify(health)}`);
    } catch (e) {
        log(`Health check failed: ${e.message}`);
        return;
    }

    // 2. Compile
    const code = `package examples
import chisel3._
class Empty extends Module {
  val io = IO(new Bundle {})
}
`;
    log("Compiling Empty module...");
    try {
        const result = await compilationService.compile(code, "Empty", {});
        if (result.success) {
            log("Compilation successful!");
            log(`Verilog: ${result.verilog.substring(0, 50)}...`);
        } else {
            log(`Compilation failed: ${result.error}`);
            return;
        }
    } catch (e) {
        log(`Compilation exception: ${e.message}`);
        return;
    }

    // 3. Verify (Mock verify since Empty has no props, but checks worker)
    log("Verifying Empty module...");
    try {
        // We need verilog for verification
        const verilog = "module Empty(); endmodule"; 
        const result = await compilationService.verify("Empty", {}, verilog);
        log(`Verification result: ${JSON.stringify(result)}`);
    } catch (e) {
        log(`Verification exception: ${e.message}`);
    }
}

window.runDebugFlow = runDebugFlow;
export default runDebugFlow;
