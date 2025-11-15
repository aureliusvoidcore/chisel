# Web Integration

The page `pages/formal-verification-hwcbmc.html` loads `/hwcbmc_build/hwcbmc.js` and the wrapper `hwcbmc-wrapper.js`.

Expected Emscripten settings:
- `-s MODULARIZE=1 -s EXPORT_NAME=HWCBMCModule`
- `-s ENVIRONMENT=web,worker`
- `-s ALLOW_MEMORY_GROWTH=1`

The wrapper uses `callMain(argv)` to invoke the CLI. The UI writes the Verilog file to the in-memory FS and constructs arguments like:

```
hw-cbmc design.v --top top --bound 20 --show-trace --vcd trace.vcd
```

After a run, use the Virtual Filesystem panel to download artifacts (e.g., `trace.vcd`).
