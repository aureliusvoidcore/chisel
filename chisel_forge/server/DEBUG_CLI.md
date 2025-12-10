# Debug CLI Tool

Quick command-line tool to test Chisel compilation without running the full web server.

## Usage

```bash
cd server

# Test a specific module
npm run debug Empty
npm run debug SimpleAdder

# List available test modules
npm run debug:list

# Test all modules
npm run debug:all
```

## Available Test Modules

- `Empty` - Minimal module with no I/O
- `SimpleAdder` - 4-bit adder

## What It Does

1. Creates `UserModule.scala` in `chisel/src/main/scala/examples/`
2. Writes `generation_config.json`
3. Runs `make generate MODULE=<ClassName>`
4. Reads generated SystemVerilog
5. Cleans up temporary files

## Output

The tool provides colored output showing:
- ✅ Success steps (green)
- ℹ️ Information (cyan/blue)
- ⚠️ Compilation output (yellow)
- ❌ Errors (red)

## Debugging Compilation Issues

If compilation fails, the tool shows:
- Full SBT output
- Error messages from compiler
- Generated files location
- Command that was executed

This is much faster than:
1. Starting the backend server
2. Starting the frontend
3. Clicking through the UI
4. Checking server logs

## Adding Test Modules

Edit `debug-compile.js` and add to `TEST_MODULES`:

```javascript
const TEST_MODULES = {
  MyModule: `package examples

import chisel3._

class MyModule extends Module {
  val io = IO(new Bundle {
    val in = Input(UInt(8.W))
    val out = Output(UInt(8.W))
  })
  
  io.out := io.in
}`
};
```

## Exit Codes

- `0` - Success
- `1` - Compilation failed or error occurred

## Examples

### Test Empty Module
```bash
$ npm run debug Empty

[TEST] Testing compilation for module: Empty
[INFO] Session ID: 1765273034814
[INFO] Extracted class name: Empty
[OK] Wrote file: /home/diego/.../UserModule.scala
[OK] Wrote config: {"module":"Empty",...}
[COMPILE] Starting SBT compilation...
[OK] Compilation successful!

--- SBT Output ---
...

--- Generated SystemVerilog ---
module Empty(
  input clock,
        reset
);
endmodule

[CLEANUP] Removed UserModule.scala
```

### Test All Modules
```bash
$ npm run debug:all

Testing all modules...

============================================================
[TEST] Testing compilation for module: Empty
...
============================================================

============================================================
[TEST] Testing compilation for module: SimpleAdder
...
============================================================

Summary:
  Passed: 2
  Failed: 0
```

## Troubleshooting

### "make: command not found"
Install GNU Make for your system.

### "SBT compilation failed"
Check that `chisel` repository is set up:
```bash
cd ../../chisel
make setup
```

### "ENOENT: no such file or directory"
The chisel repository path may be incorrect. Check `CHISEL_ROOT` in `debug-compile.js`.

### Version conflicts
If you see Scala version conflicts, check `chisel/build.sbt` and ensure ScalaJS is disabled.

## Performance

- First compilation: ~10-15 seconds (SBT startup + compilation)
- Subsequent compilations: ~3-5 seconds (SBT cached)
- Testing all modules: ~30-60 seconds

## Integration with CI/CD

You can use this in automated testing:

```bash
#!/bin/bash
# test-compilation.sh

cd server

# Test all modules
npm run debug:all

if [ $? -ne 0 ]; then
  echo "❌ Compilation tests failed"
  exit 1
fi

echo "✅ All compilation tests passed"
```

## vs Web Server Testing

| Aspect | Debug CLI | Web Server |
|--------|-----------|------------|
| Speed | Fast | Slower (HTTP overhead) |
| Setup | Just run | Start 2 servers |
| Debugging | Direct output | Check browser + server logs |
| Isolation | Single test | Full stack |
| CI/CD | Easy | Complex |

Use the debug CLI for:
- Quick iteration during development
- Testing specific modules
- Debugging compilation issues
- Automated testing
- CI/CD pipelines

Use the web server for:
- Full integration testing
- UI workflow testing
- End-to-end verification
- Demonstration
