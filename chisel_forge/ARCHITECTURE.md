# ChiselForge - Web-Based Chisel IDE

ChiselForge is a web-based integrated development environment for [Chisel](https://www.chisel-lang.org/) hardware design, featuring real-time compilation, SystemVerilog generation, and formal verification.

## Architecture

ChiselForge uses a **client-server architecture** to provide authentic Chisel compilation following the same build flow as the standalone `chisel` repository:

```
┌─────────────────────────────────────────────────────────────┐
│ Frontend (React + Vite)                                     │
│  ├─ Monaco Editor (Scala syntax highlighting)              │
│  ├─ Compilation API Client                                 │
│  └─ HWCBMC/EBMC Verification (WebAssembly)                 │
└────────────────────┬────────────────────────────────────────┘
                     │ HTTP POST /api/compile
                     │ { code, moduleName, config }
                     ▼
┌─────────────────────────────────────────────────────────────┐
│ Backend Server (Node.js + Express)                         │
│  1. Receives Chisel code from browser                      │
│  2. Writes to chisel/src/main/scala/examples/              │
│  3. Executes: make generate MODULE=UserModule              │
│  4. Reads generated SystemVerilog from chisel/generated/   │
│  5. Returns { verilog, firrtl, errors }                    │
└────────────────────┬────────────────────────────────────────┘
                     │ Invokes
                     ▼
┌─────────────────────────────────────────────────────────────┐
│ Chisel Build System (SBT + CIRCT/firtool)                  │
│  ├─ SBT compiles Scala → Chisel IR                         │
│  ├─ Chisel elaborates to FIRRTL                            │
│  └─ firtool converts FIRRTL → SystemVerilog                │
└─────────────────────────────────────────────────────────────┘
```

### Why This Architecture?

Unlike [Scastie](https://scastie.scala-lang.org/), which runs generic Scala code, ChiselForge needs:

1. **Full Chisel toolchain**: Chisel + CIRCT (firtool binary) for FIRRTL → Verilog conversion
2. **Native build flow**: Must replicate the exact compilation pipeline from the `chisel` repository
3. **Hardware-specific configuration**: Layer control, verification modes, assertion strategies

**Why not Scala.js?** 
- firtool is a C++ binary (LLVM/MLIR-based) and cannot run in the browser
- Chisel elaboration requires JVM features not available in Scala.js
- The full compilation pipeline needs filesystem access for multi-file generation

## Prerequisites

### Required Software

- **Node.js** 18+ and npm
- **Java JDK** 11+ (for SBT/Scala)
- **Make** (build orchestration)
- The **chisel** repository must be set up at `../chisel/`

### Chisel Repository Setup

The backend server requires the `chisel` repository to be configured:

```bash
# Navigate to chisel directory (should be sibling to chisel_forge)
cd ../chisel

# Download and install SBT locally
make setup

# Verify it works by generating an example
make defconfig
make generate
```

## Installation

### 1. Install Backend Dependencies

```bash
cd server
npm install
```

### 2. Install Frontend Dependencies

```bash
cd ..
npm install
```

## Development

### Start the Backend Server

```bash
cd server
npm start
```

The backend server will start on `http://localhost:3001` and provide:
- `GET /api/health` - Health check
- `POST /api/compile` - Compile Chisel code
- `GET /api/examples` - List available examples
- `GET /api/examples/:name` - Get example source code

### Start the Frontend Dev Server

In a separate terminal:

```bash
npm run dev
```

The frontend will be available at `http://localhost:5173` (or the port Vite assigns).

## How It Works

### Compilation Flow

1. **User writes Chisel code** in the Monaco editor
2. **Click "Elaborate"** sends code to backend via `POST /api/compile`
3. **Backend creates temporary file**: `chisel/src/main/scala/examples/UserModule_<uuid>.scala`
4. **Backend writes config**: `chisel/generation_config.json`
5. **Backend executes**: `cd chisel && make generate MODULE=UserModule_<uuid>`
6. **SBT + Chisel + firtool** generate SystemVerilog in `chisel/generated/UserModule_<uuid>/`
7. **Backend reads** the generated `.sv` file
8. **Backend returns** JSON with `{ success, verilog, firrtl, stdout, stderr, errors }`
9. **Frontend displays** the SystemVerilog and logs

### Verification Flow

After elaboration, users can click **"Verify"** to run formal verification using HWCBMC (EBMC) compiled to WebAssembly:

1. SystemVerilog is written to the HWCBMC virtual filesystem
2. EBMC runs bounded model checking on assertions
3. Results are displayed in the verification panel

## Configuration

### Frontend Environment Variables

Create `.env.development` for development:

```bash
VITE_API_URL=http://localhost:3001/api
```

For production deployment, create `.env.production`:

```bash
VITE_API_URL=/api
```

### Backend Configuration

The backend automatically locates the chisel repository at:

```javascript
const CHISEL_ROOT = path.resolve(__dirname, '../../chisel');
```

Adjust this path in `server/server.js` if your directory structure differs.

## Building for Production

### Build Frontend

```bash
npm run build
```

This creates optimized static files in `dist/`.

### Production Deployment

For production, you'll need to:

1. **Run the backend server** on your production host
2. **Serve the frontend** via Nginx/Apache or integrate with the Node.js server
3. **Ensure the chisel repository** is accessible to the backend process

Example production setup with Nginx:

```nginx
# Serve static frontend
location / {
    root /path/to/chisel_forge/dist;
    try_files $uri /index.html;
}

# Proxy API requests to backend
location /api/ {
    proxy_pass http://localhost:3001/api/;
}
```

## Comparison with Native Chisel Workflow

| Feature | Native `chisel` | ChiselForge |
|---------|----------------|-------------|
| Code Editor | Any IDE/editor | Monaco (browser) |
| Compilation | `make generate` | Backend API + make |
| Verilog Output | `generated/` directory | Displayed in UI + API response |
| Verification | Terminal EBMC | EBMC WebAssembly in browser |
| Configuration | menuconfig or JSON | JSON via API |
| Module Selection | Command line arg | UI dropdown |

**Key Advantage**: ChiselForge provides the exact same build pipeline as the native workflow but wrapped in a web interface.

## Troubleshooting

### Backend server won't start

- **Check Java/JDK**: `java -version` should show 11+
- **Check chisel setup**: Try `cd ../chisel && make generate`
- **Check port**: Ensure port 3001 is not in use

### Compilation fails

- **Check logs**: Backend console shows SBT output
- **Verify chisel repo**: Test native compilation first
- **Check file paths**: Backend needs write access to `chisel/src/main/scala/examples/`

### Verification fails

- **Check Verilog**: Must have valid SystemVerilog with module definition
- **EBMC WASM**: Check browser console for WASM loading errors
- **Module name**: Top module must match the name passed to EBMC

## Technical Details

### Why Not Mock/Client-Side Compilation?

The initial attempt at ChiselForge used a mock compiler (`chisel-sandbox-fastopt.js`) that did regex parsing. This approach failed because:

1. **No real elaboration**: Cannot handle Chisel's hardware construction semantics
2. **No FIRRTL generation**: Chisel's IR is complex and cannot be faked
3. **No firtool**: The CIRCT toolchain is C++ and cannot run in browsers
4. **Limited Scala.js support**: Chisel 7.x doesn't fully support Scala.js compilation

### Following the Native Flow

The `chisel` repository uses:
- **VerilogGenerator.scala**: Main entry point with `ChiselStage.emitSystemVerilog()`
- **generation_config.json**: Configuration for module selection and firtool options
- **Makefile**: Orchestrates SBT and firtool invocations

ChiselForge replicates this exactly, ensuring 100% compatibility with the native workflow.

## Future Enhancements

- [ ] WebSocket streaming for real-time compilation progress
- [ ] Syntax error highlighting in editor (LSP integration)
- [ ] Waveform viewer for verification counterexamples
- [ ] Multi-file project support
- [ ] GitHub integration for saving/loading projects
- [ ] Collaboration features (shared editing sessions)

## License

See LICENSE file in repository root.

## Credits

- **Chisel**: https://github.com/chipsalliance/chisel
- **CIRCT**: https://circt.llvm.org/
- **EBMC/HW-CBMC**: Formal verification tools
- **Monaco Editor**: Microsoft's code editor
- **Scastie**: Inspiration for web-based Scala compilation architecture
