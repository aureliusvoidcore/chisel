// API Service for ChiselForge.
//
// This app supports two runtime modes:
// - Server mode: uses the Node backend endpoints (./api/*) for Chisel elaboration and EBMC.
// - Static mode (GitHub Pages): no backend; loads pre-generated SystemVerilog from dist/generated
//   and runs formal verification in-browser via hwcbmc WebAssembly (dist/bin).

import FileSystem from './fileSystem';
import { EXAMPLES } from './examples';

const BASE_URL = (import.meta.env.BASE_URL ?? './');

function joinUrl(base, path) {
  if (!base.endsWith('/')) base += '/';
  if (path.startsWith('/')) path = path.slice(1);
  return base + path;
}

function isFileProtocol() {
  try {
    return typeof window !== 'undefined' && window.location && window.location.protocol === 'file:';
  } catch {
    return false;
  }
}

async function fetchWithTimeout(url, opts = {}, timeoutMs = 1500) {
  const controller = new AbortController();
  const timer = setTimeout(() => controller.abort(), timeoutMs);
  try {
    return await fetch(url, { ...opts, signal: controller.signal });
  } finally {
    clearTimeout(timer);
  }
}

function parseVerificationResults(output) {
  const results = {
    proved: [],
    failed: [],
    inconclusive: [],
    unsupported: []
  };

  const parts = output.split('** Results:');
  if (parts.length < 2) return results;

  const resultsSection = parts[1];
  const lines = resultsSection.split('\n');
  for (const line of lines) {
    if (line.includes('PROVED')) {
      const match = line.match(/\[([\w$.]+)\]\s+(.*?):\s+PROVED/);
      if (match) results.proved.push({ property: match[1], description: match[2] });
    } else if (line.includes('FAILED') || line.includes('REFUTED')) {
      const match = line.match(/\[([\w$.]+)\]\s+(.*?):\s+(FAILED|REFUTED)/);
      if (match) results.failed.push({ property: match[1], description: match[2] });
    } else if (line.includes('INCONCLUSIVE')) {
      const match = line.match(/\[([\w$.]+)\]\s+(.*?):\s+INCONCLUSIVE/);
      if (match) results.inconclusive.push({ property: match[1], description: match[2] });
    } else if (line.includes('UNSUPPORTED')) {
      const match = line.match(/\[([\w$.]+)\]\s+(.*?):\s+UNSUPPORTED/);
      if (match) results.unsupported.push({ property: match[1], description: match[2] });
    }
  }
  return results;
}

function detectLayerDefinesFromSv(svText) {
  const found = new Set();
  const re = /^\s*`ifdef\s+(layer[^\s]+)\s*$/gm;
  let m;
  while ((m = re.exec(svText)) !== null) {
    found.add(m[1]);
  }
  return Array.from(found);
}

function splitCommaList(value) {
  if (!value) return [];
  if (Array.isArray(value)) return value.flatMap(splitCommaList);
  return String(value)
    .split(',')
    .map((s) => s.trim())
    .filter(Boolean);
}

let hwcbmcLoadPromise = null;
async function ensureHwcbmcLoaded() {
  if (hwcbmcLoadPromise) return hwcbmcLoadPromise;

  if (isFileProtocol()) {
    throw new Error(
      'Static mode cannot load WebAssembly from file:// URLs. Serve the site over HTTP (e.g. `npm run preview`) or use GitHub Pages.'
    );
  }

  hwcbmcLoadPromise = (async () => {
    const loadScript = (src) =>
      new Promise((resolve, reject) => {
        const existing = document.querySelector(`script[data-chiselforge-src="${src}"]`);
        if (existing) {
          resolve();
          return;
        }
        const s = document.createElement('script');
        s.src = src;
        s.async = true;
        s.dataset.chiselforgeSrc = src;
        s.onload = () => resolve();
        s.onerror = () => reject(new Error(`Failed to load ${src}`));
        document.head.appendChild(s);
      });

    await loadScript(joinUrl(BASE_URL, 'bin/hwcbmc.js'));
    await loadScript(joinUrl(BASE_URL, 'bin/hwcbmc-wrapper.js'));

    if (typeof window === 'undefined' || typeof window.HWCBMCWrapper === 'undefined') {
      throw new Error('HWCBMCWrapper not available after script load');
    }
  })();

  return hwcbmcLoadPromise;
}

class CompilationService {
  constructor() {
    this.fs = new FileSystem();
    this.fs.init().catch(e => console.error("FS Init failed", e));

    // 'server' (backend available) | 'static' (GitHub Pages) | 'unknown'
    this.mode = 'unknown';
  }

  /**
   * Check if the backend is available
   */
  async health() {
    // Production builds are intended for static hosting (GitHub Pages) and do not have a backend.
    // Avoid probing /api/health on static hosts, which creates noisy 404s in the console.
    if (import.meta.env.PROD) {
      this.mode = 'static';
      return { status: 'ok', mode: 'static' };
    }

    try {
      const res = await fetchWithTimeout(
        joinUrl(BASE_URL, 'api/health'),
        { headers: { Accept: 'application/json' } },
        1200,
      );

      // On static hosts (Vite preview, GitHub Pages), unknown routes often return index.html (200).
      // Treat non-JSON responses as "no backend".
      const contentType = (res.headers.get('content-type') || '').toLowerCase();
      if (res.ok && contentType.includes('application/json')) {
        const data = await res.json().catch(() => null);
        if (data && (data.status === 'ok' || data.ok === true)) {
          this.mode = 'server';
          return { status: 'ok', mode: 'server' };
        }
      }

      this.mode = 'static';
      return { status: 'ok', mode: 'static' };
    } catch (e) {
      this.mode = 'static';
      return { status: 'ok', mode: 'static', error: e.message };
    }
  }

  /**
   * Compile Chisel code to Verilog using the backend server
   */
  async compile(code, moduleName = 'UserModule', config = {}) {
    // Prefer server if available
    if (this.mode !== 'static') {
      try {
        const response = await fetch(joinUrl(BASE_URL, 'api/compile'), {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({ code, moduleName, config })
        });

        const result = await response.json();
        if (response.ok) {
          this.mode = 'server';
          return result;
        }
        // If backend exists but returned error, propagate it
        return result;
      } catch (error) {
        // fall through to static
        this.mode = 'static';
      }
    }

    // Static/GitHub Pages mode: cannot run Scala/Chisel.
    // We only support loading pre-generated SystemVerilog for known modules.
    try {
      if (isFileProtocol()) {
        return {
          success: false,
          error: 'You are opening the site via file://. Browsers block fetch() of generated assets. Use `npm run preview` (or any HTTP server) to run the built dist/ folder.'
        };
      }

      const expected = EXAMPLES[moduleName]?.chisel;
      if (expected && code && code.trim() !== expected.trim()) {
        return {
          success: false,
          error: 'Static mode cannot elaborate modified Chisel. Start the backend for Chisel compilation, or edit SystemVerilog directly.'
        };
      }

      const svUrl = joinUrl(BASE_URL, `generated/${moduleName}/${moduleName}.sv`);
      const res = await fetch(svUrl);
      if (!res.ok) {
        return {
          success: false,
          error: `No pre-generated SystemVerilog found for ${moduleName} at ${svUrl}`
        };
      }
      const verilog = await res.text();
      return {
        success: true,
        verilog,
        stdout: '[Static] Loaded pre-generated SystemVerilog from dist/generated',
        stderr: '',
        moduleName
      };
    } catch (error) {
      return { success: false, error: error.message };
    }
  }

  /**
   * Run formal verification using the backend server
   */
  async verify(moduleName, ebmcParams = {}, verilogCode = null) {
    // Prefer server verification if available
    if (this.mode !== 'static') {
      try {
        const response = await fetch(joinUrl(BASE_URL, 'api/verify'), {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({ moduleName, verilogCode, ebmcParams })
        });

        const result = await response.json();

        // If VCD was generated on server, fetch it and store into local FS for Surfer.
        if (result?.vcdFile) {
          try {
            const vcdUrl = joinUrl(BASE_URL, `api/files/${moduleName}/${result.vcdFile}`);
            const vcdRes = await fetch(vcdUrl);
            if (vcdRes.ok) {
              const vcdText = await vcdRes.text();
              const vcdPath = `/verification/${moduleName}/${result.vcdFile}`;
              try {
                await this.fs.createFile(vcdPath, vcdText, 'vcd');
              } catch {
                await this.fs.updateFile(vcdPath, vcdText);
              }
            }
          } catch (e) {
            console.warn('Failed to fetch/store VCD:', e);
          }
        }

        this.mode = 'server';
        return result;
      } catch (error) {
        this.mode = 'static';
        // fall through to static verification
      }
    }

    // Static verification: run in-browser via hwcbmc wasm.
    try {
      await ensureHwcbmcLoaded();
      const wrapper = new window.HWCBMCWrapper();
      await wrapper.initialize({
        locateFile: (path, prefix) => {
          // Ensure the wasm is resolved relative to the site base.
          return joinUrl(BASE_URL, `bin/${path}`);
        }
      });

      const svText = verilogCode;
      if (!svText || !svText.trim()) {
        return { success: false, error: 'No SystemVerilog provided for verification' };
      }

      const workDir = `/work/${moduleName}`;
      try {
        wrapper.module.FS.mkdir('/work');
      } catch {}
      try {
        wrapper.module.FS.mkdir(workDir);
      } catch {}

      const svPath = `${workDir}/${moduleName}.sv`;
      wrapper.writeFile(svPath, svText);

      const argv = ['--systemverilog', svPath];

      const detectedLayers = detectLayerDefinesFromSv(svText);
      const userLayers = splitCommaList(ebmcParams.layers);
      const allLayers = Array.from(new Set([...detectedLayers, ...userLayers]));
      for (const layer of allLayers) {
        argv.push('-D', layer);
      }

      if (ebmcParams.top) argv.push('--top', String(ebmcParams.top));
      if (ebmcParams.property) argv.push('--property', String(ebmcParams.property));
      if (ebmcParams.propertyExpr) argv.push('-p', String(ebmcParams.propertyExpr));

      const engine = ebmcParams.engine || ebmcParams.method;
      if (engine === 'k-induction' || engine === 'kinduction') argv.push('--k-induction');
      else if (engine === 'ic3') argv.push('--ic3');
      else if (engine === 'bdd') argv.push('--bdd');

      if (ebmcParams.bound) argv.push('--bound', String(ebmcParams.bound));
      if (ebmcParams.trace === true) argv.push('--trace');
      if (ebmcParams.waveform === true) argv.push('--waveform');
      if (ebmcParams.numberedTrace === true) argv.push('--numbered-trace');
      if (ebmcParams.showProperties === true) argv.push('--show-properties');

      let vcdFile = null;
      if (ebmcParams.vcd) {
        vcdFile = ebmcParams.vcd === true ? `${moduleName}.vcd` : String(ebmcParams.vcd);
        const vcdPath = `${workDir}/${vcdFile}`;
        argv.push('--vcd', vcdPath);
      }

      const execResult = wrapper.execute(argv);
      const stdout = execResult.stdout || '';
      const stderr = execResult.stderr || '';
      const exitCode = execResult.exitCode;

      const results = parseVerificationResults(stdout);

      // If requested, persist VCD for Surfer
      if (vcdFile) {
        const vcdPath = `${workDir}/${vcdFile}`;
        try {
          const vcdContent = wrapper.readFile(vcdPath, 'utf8');
          const storePath = `/verification/${moduleName}/${vcdFile}`;
          try {
            await this.fs.createFile(storePath, vcdContent, 'vcd');
          } catch {
            await this.fs.updateFile(storePath, vcdContent);
          }
        } catch (e) {
          // It's ok if no trace exists (e.g., all proved)
          vcdFile = null;
        }
      }

      return {
        success: true,
        moduleName,
        ebmcParams,
        exitCode,
        results,
        vcdFile,
        stdout,
        stderr
      };
    } catch (error) {
      return { success: false, error: error.message };
    }
  }

  async readFileBlob(path) {
    // Support reading from the backend static file server when in server mode.
    // Backend paths look like: /api/files/<module>/<file.vcd>
    if (typeof path === 'string' && (path.startsWith('/api/') || path.startsWith('api/'))) {
      const url = joinUrl(BASE_URL, path);
      const res = await fetch(url);
      if (!res.ok) throw new Error(`Failed to fetch: ${url} (${res.status})`);
      const content = await res.text();
      return new Blob([content], { type: 'text/plain' });
    }

    await this.fs.ensureReady?.();
    const file = await this.fs.readFile(path);
    if (!file) throw new Error(`File not found: ${path}`);

    const content = file.content ?? '';
    return new Blob([content], { type: 'text/plain' });
  }

  // File System Proxy Methods
  async listFiles() {
    // Always include local IndexedDB files (e.g., /verification/* created in static mode,
    // or persisted after a server-mode verification run).
    await this.fs.ensureReady?.();
    const localFiles = (await this.fs.listFiles()) || [];

    // Optionally merge backend-generated files (when server is reachable).
    if (this.mode === 'unknown') await this.health();
    if (this.mode !== 'server') return localFiles;

    try {
      const res = await fetch(joinUrl(BASE_URL, 'api/fs/list'), {
        headers: { Accept: 'application/json' }
      });
      const contentType = (res.headers.get('content-type') || '').toLowerCase();
      if (!res.ok || !contentType.includes('application/json')) return localFiles;
      const serverList = await res.json();
      const serverPaths = Array.isArray(serverList) ? serverList : (serverList?.files || []);

      const merged = new Map();
      for (const f of localFiles) {
        if (f?.path) merged.set(f.path, f);
      }
      for (const rel of serverPaths) {
        if (!rel || typeof rel !== 'string') continue;
        const p = rel.startsWith('/') ? rel : `/api/files/${rel}`;
        if (!merged.has(p)) merged.set(p, { path: p, type: 'remote' });
      }
      return Array.from(merged.values());
    } catch {
      return localFiles;
    }
  }
  async readFile(path) { return this.fs.readFile(path); }
  async createFile(path, content, type) { return this.fs.createFile(path, content, type); }
  async updateFile(path, content) { return this.fs.updateFile(path, content); }
  
  async deleteFile(fileName) {
    await this.fs.ensureReady();
    return new Promise((resolve, reject) => {
      const transaction = this.fs.db.transaction(['files'], 'readwrite');
      const store = transaction.objectStore('files');
      const request = store.delete('/' + fileName);
      request.onsuccess = () => resolve({ success: true });
      request.onerror = () => reject(request.error);
    });
  }

  async renameFile(oldName, newName) {
    const file = await this.fs.readFile('/' + oldName);
    if (!file) throw new Error("File not found");
    
    await this.deleteFile(oldName);
    await this.fs.createFile('/' + newName, file.content, file.type);
    return { success: true };
  }

  /**
   * Get list of examples from the server
   */
  async getExamples() {
    if (this.mode === 'unknown') await this.health();
    if (this.mode !== 'server') return Object.keys(EXAMPLES);

    try {
      const res = await fetch(joinUrl(BASE_URL, 'api/examples'), {
        headers: { Accept: 'application/json' }
      });
      const contentType = (res.headers.get('content-type') || '').toLowerCase();
      if (!res.ok || !contentType.includes('application/json')) throw new Error('Failed to fetch examples');
      const data = await res.json();
      return (data.examples || []).map((e) => e.name);
    } catch (e) {
      this.mode = 'static';
      if (import.meta.env.DEV) {
        console.warn('Failed to fetch examples from server; using static examples.', e);
      }
      return Object.keys(EXAMPLES);
    }
  }

  /**
   * Get example content from the server
   */
  async getExample(name) {
    if (this.mode === 'unknown') await this.health();
    if (this.mode !== 'server') {
      if (!EXAMPLES[name]) throw new Error(`Unknown example: ${name}`);
      return EXAMPLES[name].chisel;
    }

    try {
      const res = await fetch(joinUrl(BASE_URL, `api/examples/${name}`), {
        headers: { Accept: 'application/json' }
      });
      const contentType = (res.headers.get('content-type') || '').toLowerCase();
      if (!res.ok || !contentType.includes('application/json')) throw new Error('Failed to fetch example');
      const data = await res.json();
      return data.content;
    } catch (e) {
      this.mode = 'static';
      if (import.meta.env.DEV) {
        console.warn('Failed to fetch example content from server; using static example.', e);
      }
      if (!EXAMPLES[name]) throw e;
      return EXAMPLES[name].chisel;
    }
  }

  async downloadVCD(moduleName, fileName) {
    const path = `/verification/${moduleName}/${fileName}`;
    const file = await this.fs.readFile(path);
    if (!file) throw new Error("VCD file not found");
    return new Blob([file.content], { type: 'text/plain' });
  }
}

export default new CompilationService();
