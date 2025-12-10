# ChiselForge

A fully portable, web-based IDE for [Chisel](https://www.chisel-lang.org/) hardware design with integrated compilation and formal verification.

![ChiselForge Screenshot](docs/screenshot.png)

## Features

- 🖥️ **Browser-Based IDE** - Write Chisel code with Monaco editor (VS Code's editor)
- ⚡ **Real Compilation** - Uses authentic Chisel/CIRCT toolchain via backend API
- 🔍 **Formal Verification** - Integrated HWCBMC (EBMC) via WebAssembly
- 📊 **Live Results** - See generated SystemVerilog and verification results instantly
- 🎯 **Example Library** - Pre-loaded Chisel examples (Adder, Counter, ALU, etc.)
- 🎨 **Modern UI** - Clean, professional interface with syntax highlighting
- 🚀 **Fully Portable** - No hardcoded paths, works anywhere via environment variables
- 🐳 **Docker Ready** - Complete containerization for isolated deployment

## Architecture

ChiselForge uses a client-server architecture with **configurable, portable paths**:

**Frontend (React)** → **Backend (Node.js)** → **Chisel Build System (SBT + firtool)**

All paths are configured via environment variables - no hardcoded user paths!

See [ARCHITECTURE.md](ARCHITECTURE.md) and [DEPLOYMENT.md](DEPLOYMENT.md) for details.

## Quick Start

### Prerequisites

- Node.js 18+
- Java JDK 11+
- Make

### Setup

```bash
# 1. Clone repository anywhere you like
git clone <repo-url> ~/my-projects/chiselforge
cd ~/my-projects/chiselforge

# 2. Set up Chisel toolchain (installs SBT, firtool, etc.)
cd chisel
make setup
cd ../chisel_forge

# 3. Install dependencies
npm install
cd server && npm install && cd ..

# 4. Configure (optional - uses relative paths by default)
cp server/.env.example server/.env
cp .env.example .env
# Edit if needed: nano server/.env

# 5. Start development
./dev.sh
```

Open your browser to `http://localhost:5173`

### Docker Deployment (Production)

```bash
# Build and run with Docker
cd docker
docker-compose up -d

# Access at http://localhost:3001
```

See [DEPLOYMENT.md](DEPLOYMENT.md) for cloud deployment options (AWS, GCP, Azure, Kubernetes).

## Usage

1. **Select an Example** - Choose from the sidebar (Empty, Adder, Counter, etc.)
2. **Edit Code** - Modify the Chisel code in the Monaco editor
3. **Configure** - Set build options in Configuration tab (optional)
4. **Click "Elaborate"** - Compile to SystemVerilog (backend status must show "connected")
5. **View Results** - See generated Verilog in the bottom pane
6. **Click "Verify"** - Run formal verification with EBMC (optional)

## Configuration

ChiselForge is **fully portable** - configure paths via environment variables:

### Backend Configuration (server/.env)

```bash
# Path to chisel repository (defaults to ../../chisel if not set)
CHISEL_ROOT=/opt/chiselforge/chisel

# API server port
PORT=3001

# Environment
NODE_ENV=production
```

### Frontend Configuration (.env)

```bash
# Backend API URL
VITE_API_URL=http://localhost:3001/api
```

**Works anywhere!** No hardcoded paths in the code. Deploy to:
- Local development machine
- Dedicated server
- Docker container
- AWS/GCP/Azure cloud
- Kubernetes cluster

See [DEPLOYMENT.md](DEPLOYMENT.md) for complete deployment guide.

## Project Structure

```
chisel_forge/
├── src/                    # Frontend source
│   ├── App.jsx            # Main React component
│   ├── api.js             # Backend API client
│   ├── compiler.worker.js # HWCBMC WebAssembly worker
│   └── examples.js        # Example Chisel modules
├── server/                # Backend compilation server
│   ├── server.js          # Express API server
│   ├── debug-compile.js   # CLI debug tool
│   ├── .env.example       # Environment configuration template
│   └── package.json       # Backend dependencies
├── docker/                # Container deployment
│   ├── Dockerfile
│   ├── docker-compose.yml
│   └── .dockerignore
├── public/                # Static assets
│   └── bin/               # HWCBMC WASM binaries
├── ARCHITECTURE.md        # Technical architecture
├── DEPLOYMENT.md          # Deployment guide
├── QUICK_REFERENCE.md     # Developer cheat sheet
└── dev.sh                 # Development startup script

chisel/                    # Chisel native toolchain (separate repo)
├── tools/sbt/             # SBT build tool
├── tools/firtool/         # CIRCT firtool binary
├── src/main/scala/        # Chisel source
│   └── examples/          # User modules go here
├── generated/             # Generated SystemVerilog
└── Makefile               # Build orchestration
```

## How It Works

1. **Write Code**: User writes Chisel in browser
2. **Submit**: Frontend sends code to backend via `POST /api/compile`
3. **Write File**: Backend writes code to `${CHISEL_ROOT}/src/main/scala/examples/UserModule.scala`
4. **Run Make**: Backend executes `make generate MODULE=UserModule` in `${CHISEL_ROOT}`
5. **SBT Compiles**: Scala → Chisel IR → FIRRTL
6. **firtool Converts**: FIRRTL → SystemVerilog
7. **Read Output**: Backend reads generated `.sv` file from `chisel/generated/`
8. **Return Results**: Backend sends SystemVerilog + logs back to frontend
9. **Display**: Frontend shows Verilog in UI

This follows the **exact same build flow** as the native `chisel` Makefile workflow.

## Verification

ChiselForge includes HWCBMC (EBMC) compiled to WebAssembly for formal verification:

- Bounded model checking
- SystemVerilog Assertion (SVA) support
- Runs entirely in the browser
- Results displayed in verification panel

## Configuration

Backend server configuration in `server/server.js`:

```javascript
const CHISEL_ROOT = path.resolve(__dirname, '../../chisel');
const PORT = process.env.PORT || 3001;
```

Frontend API URL via `.env.development`:

```bash
VITE_API_URL=http://localhost:3001/api
```

## Building for Production

```bash
# Build frontend
npm run build

# Output in dist/
# Deploy dist/ as static files
# Ensure backend server is running and accessible
```

## Troubleshooting

### "Backend: disconnected" in status bar

- Ensure backend server is running: `cd server && npm start`
- Check backend console for errors
- Verify port 3001 is available

### Compilation fails

- Check backend console logs for SBT errors
- Test native compilation: `cd ../chisel && make generate`
- Ensure Java JDK 11+ is installed: `java -version`
- Check chisel tools are set up: `ls ../chisel/tools/sbt`

### "Cannot find chisel directory"

- Ensure chisel repository is at `../chisel/`
- Run `cd ../chisel && make setup`

## Comparison with Native Workflow

| Feature | Native Chisel | ChiselForge |
|---------|--------------|-------------|
| Editor | VS Code / IntelliJ | Monaco (browser) |
| Compile | `make generate` | Click "Elaborate" button |
| Output | `generated/` dir | Displayed in UI |
| Verification | Terminal EBMC | Browser WASM EBMC |
| Config | menuconfig / JSON | JSON via API |

## Why This Architecture?

ChiselForge **cannot use Scala.js** like Scastie because:

1. **firtool is C++** - CIRCT's FIRRTL→Verilog compiler cannot run in browsers
2. **Filesystem required** - Multi-file generation needs real filesystem
3. **JVM features** - Chisel elaboration needs full JVM capabilities

Therefore, we use a **backend server** that invokes the real Chisel build system, ensuring 100% compatibility with native workflows.

## Development

### API Endpoints

Backend server provides:

- `GET /api/health` - Health check
- `POST /api/compile` - Compile Chisel code
  ```json
  {
    "code": "package examples\n\nclass Foo extends Module { ... }",
    "moduleName": "Foo",
    "config": { "mode": "verification", "layers": "inline" }
  }
  ```
- `GET /api/examples` - List available examples
- `GET /api/examples/:name` - Get example source code

### Adding New Examples

1. Add to `src/examples.js`:
   ```javascript
   "MyModule": {
     chisel: `package examples
   
   import chisel3._
   
   class MyModule extends Module {
     // ...
   }
   `
   }
   ```

2. Module will appear in sidebar automatically

## License

See LICENSE file in repository root.

## Credits

- **Chisel**: https://github.com/chipsalliance/chisel
- **CIRCT/firtool**: https://circt.llvm.org/
- **EBMC**: Formal verification tool
- **Monaco Editor**: Microsoft's code editor
- **Scastie**: Inspiration for compilation architecture

## Contributing

Contributions welcome! Please see [ARCHITECTURE.md](ARCHITECTURE.md) for technical details.

Future enhancements:
- WebSocket streaming for compilation progress
- LSP integration for syntax checking
- Waveform viewer for verification
- Multi-file project support
- GitHub integration
