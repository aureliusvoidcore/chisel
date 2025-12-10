# ChiselForge Backend Server

This is the compilation backend for ChiselForge. It provides an HTTP API that invokes the Chisel build system to compile user code.

## Installation

```bash
npm install
```

## Running

```bash
npm start
```

Server will start on `http://localhost:3001`

## API Endpoints

### GET /api/health

Health check endpoint.

**Response:**
```json
{
  "status": "ok",
  "message": "ChiselForge compilation server running"
}
```

### POST /api/compile

Compile Chisel code to SystemVerilog.

**Request:**
```json
{
  "code": "package examples\n\nimport chisel3._\n\nclass Foo extends Module { ... }",
  "moduleName": "Foo",
  "config": {
    "mode": "verification",
    "layers": "inline",
    "preserve_values": "named",
    "randomization": "disable",
    "run_formal": "no"
  }
}
```

**Success Response (200):**
```json
{
  "success": true,
  "verilog": "module Foo(...);...",
  "firrtl": "circuit Foo : ...",
  "stdout": "SBT compilation output...",
  "stderr": "",
  "errors": null,
  "moduleName": "UserModule_abc123"
}
```

**Error Response (400/500):**
```json
{
  "success": false,
  "error": "Compilation failed",
  "stdout": "...",
  "stderr": "...",
  "errors": [
    {
      "message": "type mismatch...",
      "file": "UserModule.scala",
      "line": 10,
      "column": 5
    }
  ]
}
```

### GET /api/examples

List available example modules from chisel repository.

**Response:**
```json
{
  "examples": [
    { "name": "Adder", "file": "Adder.scala" },
    { "name": "Counter", "file": "Counter.scala" }
  ]
}
```

### GET /api/examples/:name

Get source code of a specific example.

**Response:**
```json
{
  "name": "Adder",
  "content": "package examples\n\nimport chisel3._\n\nclass Adder extends Module { ... }"
}
```

## Configuration

The server is configured via these environment variables (with defaults):

- `PORT` - Server port (default: 3001)

The chisel repository path is hardcoded in `server.js`:

```javascript
const CHISEL_ROOT = path.resolve(__dirname, '../../chisel');
```

Adjust this if your directory structure differs.

## How It Works

1. Receives POST to `/api/compile` with Chisel code
2. Generates unique session ID
3. Writes code to `chisel/src/main/scala/examples/UserModule_<uuid>.scala`
4. Writes `chisel/generation_config.json` with compilation settings
5. Executes `make generate MODULE=UserModule_<uuid>` in chisel directory
6. Reads generated SystemVerilog from `chisel/generated/UserModule_<uuid>/`
7. Parses compilation errors from stdout/stderr
8. Returns results as JSON
9. Cleans up temporary source file

## Requirements

- Node.js 18+
- The `chisel` repository must be set up at `../../chisel` (relative to server directory)
- Chisel tools must be installed: `cd ../../chisel && make setup`

## Development

For auto-reload on changes:

```bash
npm run dev
```

This uses Node's `--watch` flag to restart on file changes.

## Troubleshooting

### "Cannot find chisel directory"

Ensure the chisel repository exists at the correct path:
```bash
ls ../../chisel
```

### Compilation timeouts

The server has a 2-minute timeout for compilation. For complex modules, you may need to increase this in `server.js`:

```javascript
const result = await execAsync(sbtCommand, {
  timeout: 120000, // Increase this value
  maxBuffer: 10 * 1024 * 1024
});
```

### SBT errors

Check that SBT is working in the chisel directory:
```bash
cd ../../chisel
make generate MODULE=Adder
```

## Production Deployment

For production:

1. Use a process manager like PM2:
   ```bash
   npm install -g pm2
   pm2 start server.js --name chiselforge-backend
   ```

2. Set up reverse proxy (Nginx example):
   ```nginx
   location /api/ {
       proxy_pass http://localhost:3001/api/;
       proxy_http_version 1.1;
       proxy_set_header Upgrade $http_upgrade;
       proxy_set_header Connection 'upgrade';
       proxy_set_header Host $host;
       proxy_cache_bypass $http_upgrade;
   }
   ```

3. Consider adding rate limiting to prevent abuse
4. Add request logging for monitoring
5. Set up proper error alerting

## Security Considerations

⚠️ **Important**: This server executes arbitrary Scala code via SBT. In production:

1. **Isolate the environment**: Use Docker containers
2. **Resource limits**: Set CPU/memory limits
3. **Timeout enforcement**: Already implemented (2min timeout)
4. **Input validation**: Validate code size limits
5. **Sandboxing**: Consider running in restricted user account
6. **Rate limiting**: Prevent DoS attacks
7. **Authentication**: Add API keys if exposing publicly

Example Docker isolation:

```dockerfile
FROM openjdk:11
RUN apt-get update && apt-get install -y nodejs npm make
WORKDIR /app
COPY . .
RUN cd chisel && make setup
RUN cd chisel_forge/server && npm install
CMD ["node", "chisel_forge/server/server.js"]
```

## License

See LICENSE in repository root.
