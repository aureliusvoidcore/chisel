# ChiselForge Quick Start Guide

## TL;DR

```bash
# 1. Setup chisel repository (one time)
cd ../chisel && make setup && cd ../chisel_forge

# 2. Start everything
./dev.sh

# 3. Open browser
open http://localhost:5173
```

## What You'll See

```
┌─────────────────────────────────────────────────────────────┐
│ ChiselForge                                    [Elaborate] ▶│
├──────────────┬──────────────────────────────────────────────┤
│ Modules      │ // Chisel Code Editor                        │
│ • Empty      │ package examples                             │
│ • Adder      │                                              │
│ • Counter    │ import chisel3._                             │
│ • Mux2to1    │                                              │
│ • SimpleALU  │ class Adder extends Module {                 │
│              │   val io = IO(new Bundle {                   │
├──────────────┤     val a = Input(UInt(4.W))                 │
│ Config       │     val b = Input(UInt(4.W))                 │
│ Engine: EBMC │     val sum = Output(UInt(5.W))              │
│ Bound: 20    │   })                                         │
└──────────────┴──────────────────────────────────────────────┤
                │ // Generated SystemVerilog                  │
                │ module Adder(                               │
                │   input clock,                              │
                │   input reset,                              │
                │   input [3:0] a,                            │
                │   input [3:0] b,                            │
                │   output [4:0] sum                          │
                │ );                                          │
                │   assign sum = a + b;                       │
                │ endmodule                                   │
                └─────────────────────────────────────────────┤
Status: Backend: connected | Chisel 7.4.0 | Ready            │
└──────────────────────────────────────────────────────────────┘
```

## Step-by-Step First Use

### 1. Prerequisites Check

```bash
# Check Java
java -version  # Should be 11+

# Check Node
node --version  # Should be 18+

# Check Make
make --version

# Check chisel repository exists
ls ../chisel  # Should show Makefile, build.sbt, etc.
```

### 2. Setup Chisel Tools (First Time Only)

```bash
cd ../chisel
make setup
# Downloads SBT, takes 2-3 minutes
# Creates tools/sbt/ directory

# Test it works
make defconfig
make generate MODULE=Adder
# Should create generated/Adder/Adder.sv

cd ../chisel_forge
```

### 3. Install ChiselForge Dependencies

```bash
# Backend
cd server
npm install  # Takes 1-2 minutes
cd ..

# Frontend
npm install  # Takes 1-2 minutes
```

### 4. Start Servers

**Option A: Automatic (Recommended)**
```bash
./dev.sh
```

**Option B: Manual**
```bash
# Terminal 1 - Backend
cd server
npm start
# Should show: "ChiselForge compilation server listening on port 3001"

# Terminal 2 - Frontend
cd ..
npm run dev
# Should show: "Local: http://localhost:5173/"
```

### 5. Use the IDE

1. **Open browser**: `http://localhost:5173`

2. **Check connection**: Status bar should show "Backend: connected" (green dot)

3. **Select example**: Click "Adder" in left sidebar

4. **Elaborate**: Click purple "Elaborate" button

5. **Wait**: Takes 5-20 seconds for first compilation (SBT startup)

6. **View results**: SystemVerilog appears in bottom pane

7. **Verify (optional)**: Click blue "Verify" button to run EBMC

### 6. Write Your Own Module

1. Select "Empty" from sidebar

2. Replace with your code:
   ```scala
   package examples
   
   import chisel3._
   import chisel3.util._
   
   class MyCounter extends Module {
     val io = IO(new Bundle {
       val inc = Input(Bool())
       val out = Output(UInt(8.W))
     })
     
     val count = RegInit(0.U(8.W))
     when(io.inc) {
       count := count + 1.U
     }
     io.out := count
   }
   ```

3. Click "Elaborate"

4. See generated Verilog!

## Troubleshooting

### "Backend: disconnected"

**Check backend is running:**
```bash
curl http://localhost:3001/api/health
```

**If not, start it:**
```bash
cd server
npm start
```

**Check logs for errors in terminal**

### Compilation Fails

**Test native compilation:**
```bash
cd ../chisel
make generate MODULE=Adder
```

**Check Java:**
```bash
java -version  # Must be 11+
```

**Check SBT:**
```bash
ls ../chisel/tools/sbt
```

**View backend logs in server terminal**

### "Cannot find chisel directory"

```bash
# Check path
ls ../chisel

# If missing, clone it
cd ..
git clone <repo-url> chisel
cd chisel
make setup
cd ../chisel_forge
```

### Port Already in Use

**Backend (3001):**
```bash
# Find process
lsof -i :3001

# Kill it
kill -9 <PID>

# Or change port
cd server
PORT=3002 npm start
```

**Frontend (5173):**
```bash
# Vite will auto-increment to 5174, 5175, etc.
```

### Slow Compilation

**First compilation is slow (10-20s)** - SBT needs to start and download dependencies

**Subsequent compilations are faster (5-10s)**

**Speed tips:**
- Keep backend running between sessions
- SBT caches improve over time
- Use simpler modules for testing

## Common Workflows

### Iterative Development

1. Select example as starting point
2. Modify code in editor
3. Click "Elaborate"
4. Check for errors in right panel
5. Fix errors, repeat

### Testing Different Modules

1. Write multiple classes in one file
2. Change class name to compile different module
3. Or create separate entries in examples.js

### Verification

1. Add assertions to your Chisel:
   ```scala
   assert(io.out < 256.U, "Counter overflow")
   ```

2. Elaborate to Verilog

3. Click "Verify"

4. Check results in verification panel

## Configuration Options

### Backend Config

Edit `server/server.js`:
```javascript
const PORT = process.env.PORT || 3001;
const CHISEL_ROOT = path.resolve(__dirname, '../../chisel');
```

### Frontend Config

Edit `.env.development`:
```bash
VITE_API_URL=http://localhost:3001/api
```

### Compilation Config

Modify in `api.js` call:
```javascript
await compilationService.compile(code, moduleName, {
  mode: 'verification',        // or 'synthesis'
  layers: 'inline',            // or 'split'
  preserve_values: 'named',    // or 'all', 'none'
  randomization: 'disable'     // or 'enable'
});
```

## Next Steps

- Read [ARCHITECTURE.md](ARCHITECTURE.md) for technical details
- Read [README.md](README.md) for full documentation
- Check `examples.js` to add more examples
- Explore chisel repository for more modules

## Keyboard Shortcuts (Monaco Editor)

- `Cmd/Ctrl + S` - Save (triggers elaboration if implemented)
- `Cmd/Ctrl + F` - Find
- `Cmd/Ctrl + /` - Toggle comment
- `Cmd/Ctrl + D` - Select next occurrence
- `Alt + Up/Down` - Move line up/down
- `Shift + Alt + Up/Down` - Copy line up/down
- `Cmd/Ctrl + Shift + K` - Delete line

## Tips

1. **Keep backend running** - Faster subsequent compilations
2. **Check logs** - Backend terminal shows detailed SBT output
3. **Start simple** - Use examples as templates
4. **Test native first** - If ChiselForge fails, test in chisel repo
5. **One module at a time** - Backend only compiles the class you specify

## Resources

- Chisel Documentation: https://www.chisel-lang.org/
- FIRRTL Spec: https://github.com/chipsalliance/firrtl-spec
- CIRCT/firtool: https://circt.llvm.org/
- Monaco Editor Docs: https://microsoft.github.io/monaco-editor/

## Support

- Check [IMPLEMENTATION_SUMMARY.md](IMPLEMENTATION_SUMMARY.md) for design decisions
- Review backend logs for compilation errors
- Test native chisel workflow to isolate issues
- Ensure all prerequisites are installed
