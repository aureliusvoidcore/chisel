# ChiselForge Fixes Applied

## Issue 1: Compilation Failure - Module Name with Underscores

### Problem
```
[error] Expected whitespace character
[error] runMain VerilogGenerator UserModule_5646a81d_6e16_4668_b146_c758c0a32e4a
```

The backend was creating module names with UUIDs like `UserModule_abc123_def456` which caused SBT parsing errors.

### Root Cause
1. VerilogGenerator only recognized modules in the `knownModules` map
2. UUIDs with underscores/hyphens caused SBT command parsing issues
3. Module name didn't match the class name extracted from the code

### Solution Applied

**Backend Changes (`server/server.js`):**
1. Changed temp file name from `UserModule_{uuid}` to just `UserModule`
2. Extract actual class name from user code using regex
3. Use the extracted class name for configuration and module lookup

```javascript
// Extract the class name from code
const classMatch = code.match(/class\s+(\w+)/);
const actualClassName = classMatch ? classMatch[1] : 'UserModule';

// Use actualClassName for config and compilation
const generationConfig = {
  module: actualClassName,  // Instead of tempModuleName
  ...
};
```

**Chisel Changes (`VerilogGenerator.scala`):**
1. Added `tryLoadUserModule()` function to dynamically load classes
2. Falls back to dynamic class loading if module not in knownModules

```scala
private def tryLoadUserModule(moduleName: String): Option[() => RawModule] = {
  try {
    val className = s"examples.$moduleName"
    val clazz = Class.forName(className)
    val constructor = clazz.getConstructor()
    Some(() => constructor.newInstance().asInstanceOf[RawModule])
  } catch {
    case _: Exception => None
  }
}
```

---

## Issue 2: No Configuration Interface

### Problem
ChiselForge had no way to configure compilation options like the native `chisel` repository's menuconfig system.

### Solution Applied

Added a **Configuration Tab** in the right panel with:

### 1. Generation Configuration
- **Mode**: verification / synthesis
- **Layers**: inline / split (bind)
- **Preserve Values**: named / all / none
- **Randomization**: disable / enable
- **Run Formal**: no / default / k-induction / ic3

### 2. Firtool Options (Editable Textarea)
Pre-populated with default firtool options from `chisel/firtool_config.txt`:
```
--verification-flavor=sva
--split-verilog
--lowering-options=disallowLocalVariables,disallowMuxInlining,disallowExpressionInliningInPorts,disallowPackedArrays,noAlwaysComb,verifLabels
--no-dedup
--preserve-values=named
--disable-all-randomization
--strip-debug-info
```

### 3. Build System Info
Displays:
- Command: `make generate MODULE=YourModule`
- SBT path
- Chisel version (7.4.0)
- Scala version (2.13.14)
- CIRCT version (firtool 1.137.0)

### Implementation Details

**State Management:**
```jsx
const [config, setConfig] = useState({
  mode: 'verification',
  layers: 'inline',
  preserve_values: 'named',
  randomization: 'disable',
  run_formal: 'no'
});

const [firtoolConfig, setFirtoolConfig] = useState(`...`);
```

**Tab System:**
```jsx
const [activeTab, setActiveTab] = useState('verification');

<button onClick={() => setActiveTab('config')}>Configuration</button>
```

**Config Passthrough to Backend:**
```jsx
const result = await compilationService.compile(code, selectedModule, config);
```

---

## Files Modified

### Backend
- `server/server.js`
  - Fixed module name handling
  - Extract class name from code
  - Use actual class name for compilation

### Frontend
- `src/App.jsx`
  - Added config state
  - Added firtool config textarea
  - Added Configuration tab
  - Pass config to compile API
  
- `src/examples.js`
  - Fixed missing closing brace

### Chisel
- `src/main/scala/VerilogGenerator.scala`
  - Added dynamic module loading
  - Fallback to Class.forName() for user modules

---

## Testing

### Test Compilation
```bash
# Start servers
./dev.sh

# Or manually:
cd server && npm start &
npm run dev
```

### Test Steps
1. Open http://localhost:5173
2. Select "SimpleALU" example
3. Switch to "Configuration" tab
4. Change settings (e.g., mode to "synthesis")
5. Switch back to "Verification" tab
6. Click "Elaborate"
7. Verify SystemVerilog generates successfully
8. Check logs for compilation output

### Expected Results
- ✅ Compilation should complete without UUID parsing errors
- ✅ Generated Verilog should appear in bottom pane
- ✅ Configuration options should be applied
- ✅ Module name in output should match class name from code

---

## Configuration Options Explained

### Mode
- **verification**: Optimizes for formal verification (preserves signals, adds assertions)
- **synthesis**: Optimizes for FPGA/ASIC synthesis (may inline/optimize away signals)

### Layers
- **inline**: Embed verification properties directly in module
- **split (bind)**: Generate separate bind files for assertions

### Preserve Values
- **named**: Keep named signals in output
- **all**: Keep all intermediate values (useful for debugging)
- **none**: Aggressive optimization (minimal signal preservation)

### Randomization
- **disable**: Registers initialize to 0 (deterministic, good for verification)
- **enable**: Registers initialize randomly (more realistic for simulation)

### Run Formal
- **no**: Don't run formal verification after generation
- **default**: Run EBMC with default settings
- **k-induction**: Use k-induction algorithm
- **ic3**: Use IC3/PDR algorithm

---

## Architecture Flow with Configuration

```
User Code (Monaco Editor)
    ↓
Configuration Panel
    ├─ Generation Config (dropdown selects)
    └─ Firtool Options (textarea)
    ↓
Frontend sends to Backend:
    POST /api/compile
    {
      code: "...",
      moduleName: "SimpleALU",
      config: {
        mode: "verification",
        layers: "inline",
        ...
      }
    }
    ↓
Backend:
    1. Extract class name from code
    2. Write UserModule.scala to chisel/src/
    3. Write generation_config.json
    4. Execute: make generate MODULE=SimpleALU
    ↓
Chisel Build System:
    1. SBT compiles Scala
    2. Chisel elaborates to FIRRTL
    3. firtool converts FIRRTL → SystemVerilog
       (uses config options)
    ↓
Backend returns:
    { verilog, firrtl, stdout, stderr }
    ↓
Frontend displays results
```

---

## Future Enhancements

### Configuration Tab
- [ ] Load/save configuration presets
- [ ] Import firtool config from file
- [ ] Syntax highlighting for firtool options
- [ ] Validation of firtool options
- [ ] Real-time preview of generated command

### Compilation
- [ ] Support for custom module parameters
- [ ] Multi-file project support
- [ ] Dependency management
- [ ] Incremental compilation

### Build System Integration
- [ ] Show full Make output in realtime
- [ ] Display SBT dependency resolution
- [ ] Show firtool command being executed
- [ ] Compilation time metrics

---

## Notes

### Why Dynamic Module Loading?
The VerilogGenerator previously only supported hardcoded modules. Dynamic loading allows:
- User-defined modules to be compiled
- No need to modify VerilogGenerator for each new module
- Maintains compatibility with existing examples

### Why Extract Class Name?
- User code defines the actual class name (e.g., `class SimpleALU`)
- Backend needs to tell VerilogGenerator which module to elaborate
- Class name must match between code and config file
- Avoids UUID parsing issues in SBT commands

### Configuration Persistence
Currently config is stored in React state (lost on refresh). Future versions could:
- Save to localStorage
- Save to backend session
- Export/import config files
- URL query parameters for sharing

---

## Verification

Build successful:
```
✓ 1431 modules transformed.
dist/index.html                           0.46 kB │ gzip:  0.30 kB
dist/assets/index-BrxhZ_6T.css           14.55 kB │ gzip:  3.45 kB
dist/assets/hwcbmc-wrapper-JZ1aPFa5.js    1.22 kB │ gzip:  0.53 kB
dist/assets/index-BCM8JPSm.js           201.15 kB │ gzip: 61.93 kB
✓ built in 2.80s
```

Ready for testing!
