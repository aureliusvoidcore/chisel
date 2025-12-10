
const fs = require('fs');
const path = require('path');

// Mock browser environment
global.self = {};

// Load the mock compiler
const compilerPath = path.join(__dirname, 'public/bin/chisel-sandbox-fastopt.js');
const compilerCode = fs.readFileSync(compilerPath, 'utf8');
eval(compilerCode);

const compiler = global.self.ChiselCompiler;

console.log("Running Mock Compiler Tests...\n");

let passed = 0;
let failed = 0;

function assert(condition, message) {
    if (condition) {
        console.log(`✅ PASS: ${message}`);
        passed++;
    } else {
        console.error(`❌ FAIL: ${message}`);
        failed++;
    }
}

function assertIncludes(actual, expected, message) {
    if (actual.includes(expected)) {
        console.log(`✅ PASS: ${message}`);
        passed++;
    } else {
        console.error(`❌ FAIL: ${message}`);
        console.error(`   Expected to include: "${expected}"`);
        console.error(`   Actual: "${actual}"`);
        failed++;
    }
}

// Test 1: Simple Module (Adder)
console.log("--- Test Case 1: Simple Module (Adder) ---");
const adderOpts = compiler.getFirtoolOptions("Adder", JSON.stringify({}));
assertIncludes(adderOpts, "-o=generated/Adder/Adder.sv", "Output path for simple module");
assertIncludes(adderOpts, "--verification-flavor=sva", "SVA flavor for simple module");
assertIncludes(adderOpts, "--strip-fir-debug-info", "Strip debug info for simple module");

// Test 2: Complex Module (PWMLEDAXI)
console.log("\n--- Test Case 2: Complex Module (PWMLEDAXI) ---");
const pwmOpts = compiler.getFirtoolOptions("PWMLEDAXI", JSON.stringify({ preserve_values: "named" }));
assertIncludes(pwmOpts, "-o=generated/PWMLEDAXI", "Output dir for complex module");
assertIncludes(pwmOpts, "--split-verilog", "Split verilog for complex module");
assertIncludes(pwmOpts, "@firtool_config.txt", "Config file annotation for complex module");
assert(!pwmOpts.includes("--verification-flavor=sva"), "Should NOT include SVA flavor directly (handled by layers/config)");

// Test 3: Configuration Options
console.log("\n--- Test Case 3: Configuration Options ---");
const configOpts = compiler.getFirtoolOptions("Adder", JSON.stringify({ preserve_values: "all", randomization: "disable" }));
assertIncludes(configOpts, "--preserve-values=all", "Preserve values = all");
assertIncludes(configOpts, "--disable-all-randomization", "Disable randomization");

// Test 4: Elaborate Output
console.log("\n--- Test Case 4: Elaborate Output ---");
const firrtl = compiler.elaborate("PWMLEDAXI");
assertIncludes(firrtl, "circuit PWMLEDAXI", "Circuit definition");
assertIncludes(firrtl, "layer PWMLEDAXIVerification", "Layer definition");
assertIncludes(firrtl, "layerblock PWMLEDAXIVerification.Assert", "Layerblock definition");

console.log(`\nSummary: ${passed} Passed, ${failed} Failed`);

if (failed > 0) {
    process.exit(1);
}
