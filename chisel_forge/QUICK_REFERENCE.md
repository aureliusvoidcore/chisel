# Quick Reference - ChiselForge Development

## Quick Start

```bash
# Test compilation (fastest)
cd server && npm run debug Empty

# Start full stack
./dev.sh

# Start backend only
cd server && npm start

# Start frontend only
npm run dev
```

## Debug CLI Commands

```bash
cd server

# Test one module
npm run debug Empty
npm run debug SimpleAdder

# Test all modules
npm run debug:all

# List available modules
npm run debug:list
```

## Common Issues & Fixes

### "Backend: disconnected" in browser
```bash
cd server && npm start
```

### Compilation fails
```bash
# Quick test
cd server && npm run debug Empty

# Check chisel setup
cd ../chisel && make setup
```

### SBT version conflicts
Fixed! ScalaJS is now disabled in `chisel/build.sbt`

### Module not found
Module class name must match what you pass to the API

## File Locations

```
chisel_forge/
├── server/
│   ├── server.js              # Backend API server
│   ├── debug-compile.js       # Debug CLI tool ⭐
│   └── package.json           # Backend deps + scripts
├── src/
│   ├── App.jsx                # Main UI with config tab
│   ├── api.js                 # Backend API client
│   └── examples.js            # Example modules
├── dev.sh                     # Start everything ⭐
└── COMPILATION_FIXES.md       # What we just fixed ⭐

chisel/
├── build.sbt                  # ScalaJS disabled ⭐
├── src/main/scala/
│   ├── VerilogGenerator.scala # JSExport commented out ⭐
│   └── examples/
│       └── UserModule.scala   # Temp file (auto-created)
└── generated/                 # Output directory
```

## Development Cycle

### Option 1: Fast (Debug CLI)
1. Write Chisel code
2. Add to `server/debug-compile.js` TEST_MODULES
3. Run `npm run debug YourModule`
4. See results immediately

### Option 2: Full Stack
1. Start `./dev.sh`
2. Edit code in browser
3. Click "Elaborate"
4. View output

## API Endpoints

```bash
# Health check
curl http://localhost:3001/api/health

# Compile
curl -X POST http://localhost:3001/api/compile \
  -H "Content-Type: application/json" \
  -d '{"code":"...","moduleName":"Test","config":{}}'

# Get examples
curl http://localhost:3001/api/examples
```

## Configuration

Edit `src/App.jsx` config tab or send via API:

```json
{
  "mode": "verification",
  "layers": "inline", 
  "preserve_values": "named",
  "randomization": "disable",
  "run_formal": "no"
}
```

## Build Commands

```bash
# Frontend
npm run build        # Production build
npm run dev          # Development server
npm run preview      # Preview production build

# Backend
cd server
npm start            # Production mode
npm run dev          # Auto-reload on changes
npm run debug Empty  # Test compilation
```

## Troubleshooting

### Check backend is running
```bash
curl http://localhost:3001/api/health
# Should return: {"status":"ok",...}
```

### Test compilation directly
```bash
cd server && npm run debug Empty
# Should show green [OK] messages
```

### Check chisel setup
```bash
cd ../chisel
ls tools/sbt/bin/sbt  # Should exist
make generate MODULE=Adder  # Should work
```

### Clear SBT cache
```bash
cd ../chisel
rm -rf target project/target
```

## Performance

- Debug CLI: 3-5 seconds per test
- First compilation: 10-15 seconds (SBT startup)
- Subsequent: 3-5 seconds (cached)
- Web UI: 10-20 seconds (HTTP + UI overhead)

## Key Changes Made Today

1. ✅ Disabled ScalaJS in `chisel/build.sbt`
2. ✅ Fixed Scala version conflicts
3. ✅ Commented out JSExport code
4. ✅ Created debug CLI tool
5. ✅ Added configuration tab to UI
6. ✅ Fixed module name extraction

## Success Indicators

```bash
$ npm run debug Empty
[OK] Compilation successful!
✓

$ curl http://localhost:3001/api/health
{"status":"ok"}
✓

$ npm run build
✓ built in 2.80s
✓
```

## Next Steps

1. Test web UI: `./dev.sh` → http://localhost:5173
2. Try all examples: `cd server && npm run debug:all`
3. Add your own modules to examples.js
4. Customize config in Configuration tab

## Quick Tests

```bash
# All these should work now:

# 1. Debug CLI
cd server && npm run debug Empty

# 2. Web server compile
curl -X POST http://localhost:3001/api/compile \
  -H "Content-Type: application/json" \
  -d '{"code":"package examples\nimport chisel3._\nclass Test extends Module { val io = IO(new Bundle {}) }","moduleName":"Test"}'

# 3. Full UI
./dev.sh
# → Open browser to http://localhost:5173
# → Select "Empty"  
# → Click "Elaborate"
# → Should show SystemVerilog output
```

## Help

- `server/DEBUG_CLI.md` - Debug tool documentation
- `ARCHITECTURE.md` - System architecture
- `COMPILATION_FIXES.md` - What was fixed today
- `README.md` - Full project documentation
