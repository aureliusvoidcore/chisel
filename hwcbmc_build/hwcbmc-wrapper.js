// HW-CBMC / EBMC WebAssembly wrapper
//
// Expects Emscripten build with:
//   -s MODULARIZE=1 -s EXPORT_NAME=HWCBMCModule
//   -s ENVIRONMENT=web,worker
//   -s ALLOW_MEMORY_GROWTH=1

class HWCBMCWrapper {
	constructor() {
		this.module = null;
		this.ready = false;
		this.outputBuffer = [];
		this.errorBuffer = [];
	}

	async initialize(overrides = {}) {
		if (this.ready) return;

		const baseConfig = {
			print: (t) => {
				console.log(t);
				this.outputBuffer.push(t);
			},
			printErr: (t) => {
				console.error(t);
				this.errorBuffer.push(t);
			},
			noInitialRun: true,
			locateFile: (path, prefix) => {
				if (path.endsWith('.wasm')) {
					return prefix + path;
				}
				return prefix + path;
			}
		};

		const cfg = { ...baseConfig, ...overrides };

		if (typeof HWCBMCModule === 'undefined') {
			throw new Error('HWCBMCModule factory not found. Make sure hwcbmc.js is loaded.');
		}

		this.module = await HWCBMCModule(cfg);
		this.ready = true;
	}

	writeFile(name, content) {
		if (!this.ready) throw new Error('HW-CBMC module not initialized');
		this.module.FS.writeFile(name, content);
	}

	readFile(name, encoding = 'utf8') {
		if (!this.ready) throw new Error('HW-CBMC module not initialized');
		return this.module.FS.readFile(name, { encoding });
	}

	listFiles(path = '/') {
		if (!this.ready) throw new Error('HW-CBMC module not initialized');
		return this.module.FS.readdir(path).filter((f) => f !== '.' && f !== '..');
	}

	execute(argv) {
		if (!this.ready) throw new Error('HW-CBMC module not initialized');

		this.outputBuffer = [];
		this.errorBuffer = [];

		let code = 0;
		try {
			code = this.module.callMain(argv);
		} catch (e) {
			this.errorBuffer.push(String(e));
			code = -1;
		}

		return {
			exitCode: code,
			success: code === 0,
			stdout: this.outputBuffer.join('\n'),
			stderr: this.errorBuffer.join('\n')
		};
	}
}

if (typeof window !== 'undefined') {
	window.HWCBMCWrapper = HWCBMCWrapper;
}
