# ChiselForge Compilation Flow

## Overview

ChiselForge provides a web-based IDE for compiling Chisel hardware descriptions to SystemVerilog. This document explains the complete compilation flow from user code to hardware description output.

## Architecture

```
Frontend (React)  →  Backend (Express.js)  →  Chisel/SBT  →  FIRRTL  →  firtool  →  SystemVerilog
     ↓                      ↓                      ↓            ↓           ↓              ↓
  Monaco Editor      File Management       Elaboration    IR Transform  Lowering    .sv Output
```

## Compilation Pipeline

### 1. Frontend Request (`src/App.jsx`)

When a user clicks "Compile", the frontend initiates the compilation:

```javascript
handleCompile()
  ↓
  Validates module name
  ↓
  Collects configuration (mode, layers, preserve_values, etc.)
  ↓
  Calls compilationService.compile(code, moduleName, config)
```

**Configuration Options:**
- `mode`: 'verification' or 'synthesis' - determines firtool optimization level
- `layers`: 'inline' or 'bind' - how verification properties are embedded
- `preserve_values`: 'named', 'all', or 'none' - debug information preservation
- `randomization`: 'enable' or 'disable' - controls register initialization
- `run_formal`: 'yes' or 'no' - whether to run EBMC after compilation

### 2. API Communication (`src/api.js`)

The API service sends an HTTP POST request:

```javascript
POST /api/compile
Body: {
  code: "package examples\n...",
  moduleName: "Adder",
  config: { mode: "verification", layers: "inline", ... }
}
```

### 3. Backend Reception (`server/server.js`)

The Express server receives the request and processes it:

#### 3.1 Security Validation
```javascript
// Reject malicious code patterns
if (code.includes('sys.process') || 
    code.includes('Runtime.getRuntime') || 
    code.includes('ProcessBuilder')) {
  return 400 error
}
```

#### 3.2 File Preparation
```javascript
// Ensure code is in examples package
if (!code.includes('package examples')) {
  code = 'package examples\n' + code
}

// Write to chisel/src/main/scala/examples/{ModuleName}.scala
await fs.writeFile(userFile, processedCode, 'utf-8')
```

#### 3.3 Configuration File
```javascript
// Write generation_config.json for the build system
{
  "module": "Adder",
  "mode": "verification",
  "layers": "inline",
  "preserve_values": "named",
  "randomization": "disable",
  "run_formal": "no"
}
```

### 4. Makefile Orchestration (`chisel/Makefile`)

The server executes: `make generate MODULE=Adder`

The Makefile coordinates the compilation:

```makefile
generate:
  # 1. Load configuration from generation_config.json
  MODE := $(shell jq -r '.mode // "verification"' generation_config.json)
  
  # 2. Determine firtool options based on mode
  ifeq ($(MODE),verification)
    FIRTOOL_OPTS := --verification-flavor=sva --no-dedup --preserve-values=named
  else
    FIRTOOL_OPTS := --lowering-options=... (synthesis options)
  endif
  
  # 3. Run SBT to elaborate Chisel → FIRRTL
  sbt "runMain VerilogGenerator $(MODULE)"
```

### 5. Chisel Elaboration (`chisel/src/main/scala/VerilogGenerator.scala`)

The VerilogGenerator object performs the compilation:

```scala
object VerilogGenerator extends App {
  // 1. Parse command line arguments
  val moduleName = args(0)  // e.g., "Adder"
  
  // 2. Load configuration
  val config = loadConfig("generation_config.json")
  
  // 3. Get module constructor from registry
  val knownModules = Map(
    "Adder" -> (() => new examples.Adder),
    "Counter" -> (() => new examples.Counter),
    // ... other modules
  )
  val moduleGen = knownModules(moduleName)
  
  // 4. Build firtool options based on config
  val firtoolOpts = buildFirtoolOptions(config)
  
  // 5. Elaborate: Chisel → FIRRTL → SystemVerilog
  ChiselStage.emitSystemVerilog(
    moduleGen(),
    firtoolOpts = firtoolOpts,
    args = Array("--target-dir", s"generated/$moduleName")
  )
}
```

### 6. FIRRTL Transformation

ChiselStage internally performs:

```
Chisel IR  →  CHIRRTL  →  High FIRRTL  →  Middle FIRRTL  →  Low FIRRTL
```

**Transformations include:**
- Type inference
- Width inference
- Conditional expansion
- Memory lowering
- Register initialization

### 7. firtool Lowering

The CIRCT firtool compiler converts FIRRTL to SystemVerilog:

```bash
firtool \
  -o=generated/Adder/Adder.sv \
  --verification-flavor=sva \
  --lowering-options=disallowPackedArrays,disallowLocalVariables,verifLabels \
  --strip-fir-debug-info \
  --no-dedup \
  --preserve-values=named \
  --disable-all-randomization
```

**Key Options:**
- `--verification-flavor=sva`: Generate SystemVerilog Assertions
- `--no-dedup`: Disable deduplication (preserves module structure)
- `--preserve-values=named`: Keep named signals for debugging
- `--disable-all-randomization`: Remove random initial values

### 8. Output Generation

firtool produces:

```
generated/
  Adder/
    Adder.sv          # Main SystemVerilog module
    Adder.anno.json   # Annotations (metadata)
    Adder.fir         # FIRRTL intermediate representation (if preserved)
```

### 9. Backend Response

The server sends back to frontend:

```json
{
  "success": true,
  "moduleName": "Adder",
  "verilog": "module Adder(\n  input  clock,\n  ...",
  "logs": "Generating Verilog for module: Adder\n...",
  "outputPath": "generated/Adder/Adder.sv"
}
```

### 10. Frontend Display

The frontend processes the response:

```javascript
// Update logs
setLogs([...logs, result.logs])

// Display SystemVerilog in split view
setGeneratedVerilog(result.verilog)

// Update UI state
setIsCompiling(false)
setCompilationSuccess(true)
```

## Configuration Deep Dive

### Mode: Verification vs Synthesis

**Verification Mode:**
- Purpose: Generate testbench-friendly RTL with assertions
- Options: `--verification-flavor=sva`, `--preserve-values=named`, `--disable-all-randomization`
- Use case: Formal verification with EBMC, simulation, debugging

**Synthesis Mode:**
- Purpose: Generate optimized RTL for FPGA/ASIC synthesis
- Options: `--lowering-options=...`, deduplication enabled, minimal debug info
- Use case: Production hardware, area/timing optimization

### Layers: Inline vs Bind

**Inline Mode:**
- Verification properties embedded directly in module
- Single .sv file output
- Simpler, but clutters main module code

**Bind Mode:**
- Verification properties in separate bind files
- Multiple .sv files: `Module.sv`, `Module_verification.sv`
- Cleaner separation, industry standard practice

### Preserve Values

**named:** Keep signals with explicit names in Chisel code
**all:** Keep all intermediate signals (verbose, large files)
**none:** Remove all debug information (smallest output)

## Error Handling

### Compilation Errors

**Scala Compilation Errors:**
```
[error] src/main/scala/examples/Adder.scala:10: type mismatch
```
- Caught by SBT during elaboration
- Returned in response.logs
- Displayed in terminal panel with red text

**FIRRTL Errors:**
```
[error] Width mismatch: expected 8 bits, got 4 bits
```
- Caught during FIRRTL transformation
- Indicates Chisel IR issues
- Shows line number and suggestion

**firtool Errors:**
```
Error: Cannot lower operation 'firrtl.invalid'
```
- Indicates FIRRTL construct not supported in SystemVerilog
- Usually requires Chisel code changes

### Server Errors

**Module Not Found:**
```json
{
  "error": "Module 'Foo' not found in registry",
  "availableModules": ["Adder", "Counter", ...]
}
```

**Permission Errors:**
```json
{
  "error": "Cannot write to filesystem"
}
```

## Caching Strategy

The backend implements compilation caching:

```javascript
const cacheKey = hash(code + moduleName + config)
if (compilationCache.has(cacheKey)) {
  return cached_result  // Skip compilation
}
```

**Benefits:**
- Instant response for unchanged code
- Reduces SBT startup overhead (~5-8 seconds)
- Lower CPU usage

**Cache Invalidation:**
- Automatic on code/config change
- Manual: restart server
- No persistence (in-memory only)

## Performance Characteristics

**Typical Compilation Times:**
- Simple module (Adder, Mux): 2-5 seconds
- Medium module (Counter, ALU): 5-10 seconds
- Complex module (PWMLEDAXI): 10-15 seconds

**Bottlenecks:**
1. SBT JVM startup: 3-5s (mitigated by keeping SBT running)
2. Scala compilation: 2-8s (depends on code complexity)
3. FIRRTL transformation: 1-2s
4. firtool lowering: 1-3s

## File System Layout

```
chisel_forge/
├── server/
│   └── server.js              # Backend API server
├── chisel/
│   ├── Makefile               # Build orchestration
│   ├── generation_config.json # Runtime configuration
│   ├── build.sbt              # SBT project definition
│   ├── src/main/scala/
│   │   ├── VerilogGenerator.scala    # Main compilation entry point
│   │   ├── GenerateFIRRTL.scala      # FIRRTL-only generation
│   │   ├── GenerateWithBind.scala    # Bind-mode generation
│   │   ├── FirtoolConfig.scala       # firtool option builder
│   │   └── examples/
│   │       ├── BaseModule.scala      # Base class
│   │       ├── Examples.scala        # Simple examples
│   │       └── PWMLEDAXI.scala       # Complex example
│   └── generated/                    # Compilation outputs
│       ├── Adder/
│       ├── Counter/
│       └── ...
└── src/
    ├── App.jsx                # Frontend main component
    ├── api.js                 # API service layer
    └── components/
        ├── Terminal.jsx       # Log display
        └── FileTree.jsx       # File browser
```

## Example: Complete Flow

User writes code:
```scala
class MyAdder extends BaseModule {
  val io = IO(new Bundle {
    val a = Input(UInt(4.W))
    val b = Input(UInt(4.W))
    val sum = Output(UInt(4.W))
  })
  io.sum := io.a + io.b
}
```

Frontend sends:
```json
POST /api/compile
{
  "code": "package examples\nclass MyAdder...",
  "moduleName": "MyAdder",
  "config": {"mode": "verification", "layers": "inline"}
}
```

Backend executes:
```bash
cd chisel
echo '{"module":"MyAdder",...}' > generation_config.json
make generate MODULE=MyAdder
```

Makefile runs:
```bash
sbt "runMain VerilogGenerator MyAdder"
```

VerilogGenerator:
```scala
ChiselStage.emitSystemVerilog(
  new examples.MyAdder,
  firtoolOpts = Array("--verification-flavor=sva", ...)
)
```

Output:
```systemverilog
module MyAdder(
  input  clock,
  input  reset,
  input  [3:0] io_a,
  input  [3:0] io_b,
  output [3:0] io_sum
);
  assign io_sum = io_a + io_b;
endmodule
```

Frontend displays:
- Left panel: Source code
- Right panel: Generated SystemVerilog
- Bottom panel: Compilation logs

## Debugging Tips

**Enable verbose logging:**
```javascript
// In server.js
console.log(`[${sessionId}] SBT output:`, stdout)
```

**Check intermediate FIRRTL:**
```bash
cd chisel
sbt "runMain GenerateFIRRTL MyModule"
cat generated/MyModule.fir
```

**Test firtool directly:**
```bash
firtool generated/MyModule.fir \
  --verification-flavor=sva \
  -o test.sv
```

**Inspect SBT compilation:**
```bash
cd chisel
sbt compile
# Look for errors in Scala code
```

## Common Issues

**Issue:** Module not found in registry
**Solution:** Add module to `knownModules` map in VerilogGenerator.scala

**Issue:** "package examples is not a member"
**Solution:** Ensure all Scala files have `package examples` at the top

**Issue:** Compilation timeout
**Solution:** Increase timeout in server.js or optimize Chisel code

**Issue:** Width inference error
**Solution:** Explicitly specify widths: `UInt(8.W)` instead of `UInt()`

## Future Improvements

1. **Incremental compilation:** Only recompile changed modules
2. **Parallel compilation:** Compile multiple modules simultaneously
3. **Cloud caching:** Share compilation results across users
4. **WebAssembly backend:** Run Scala/JVM in browser (eliminate backend)
5. **Live reloading:** Auto-recompile on code change
6. **Syntax highlighting:** Mark errors in Monaco editor
7. **Waveform viewer:** Integrate VCD visualization

## References

- [Chisel Documentation](https://www.chisel-lang.org/)
- [FIRRTL Specification](https://github.com/chipsalliance/firrtl-spec)
- [CIRCT firtool](https://circt.llvm.org/)
- [SystemVerilog IEEE 1800-2017](https://ieeexplore.ieee.org/document/8299595)
