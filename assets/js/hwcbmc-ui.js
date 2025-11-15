// HW-CBMC / EBMC browser UI wiring

(function () {
	let wrapper = null;
	let logBuffer = '';
	let outBuffer = '';

	function getEditorCM() {
		// Prefer the site-wide editor from editorify (CodeMirror instance)
		const cmHost = document.querySelector('.editorify-wrap .CodeMirror');
		if (cmHost && cmHost.CodeMirror) return cmHost.CodeMirror;
		return null;
	}

	function getEditorSource() {
		const cm = getEditorCM();
		if (cm) return cm.getValue();
		// Fallback to legacy textarea if present
		const srcEl = document.getElementById('hwcbmc-source');
		return (srcEl && srcEl.value) || '';
	}

	function setEditorSource(text) {
		const cm = getEditorCM();
		if (cm) { cm.setValue(text || ''); return; }
		const srcEl = document.getElementById('hwcbmc-source');
		if (srcEl) srcEl.value = text || '';
	}

	function log(line) {
		logBuffer += line + '\n';
		const el = document.getElementById('hwcbmc-log');
		if (el) {
			el.textContent = logBuffer;
			el.scrollTop = el.scrollHeight;
		}
	}

	function setStatus(text) {
		const el = document.getElementById('hwcbmc-status');
		if (el) el.textContent = text;
	}

	function appendOutput(line) {
		outBuffer += (outBuffer ? '\n' : '') + line;
		const el = document.getElementById('hwcbmc-output');
		if (el) {
			el.textContent = outBuffer;
			el.scrollTop = el.scrollHeight;
		}
	}

	function setOutput(text) {
		outBuffer = text || '';
		const el = document.getElementById('hwcbmc-output');
		if (el) {
			el.textContent = outBuffer;
			el.scrollTop = el.scrollHeight;
		}
	}

	async function ensureInit() {
		if (wrapper && wrapper.ready) return;
		if (typeof HWCBMCWrapper === 'undefined') {
			setStatus('Error: HWCBMCWrapper not found (hwcbmc-wrapper.js not loaded?)');
			return;
		}
		wrapper = new HWCBMCWrapper();
		try {
				await wrapper.initialize({
					print: (t) => { log(t); appendOutput(t); },
					printErr: (t) => { log('ERR: ' + t); appendOutput('ERR: ' + t); }
				});
			setStatus('HW-CBMC module ready.');
			log('[init] HW-CBMC / EBMC WebAssembly initialized.');

				// Attempt IC3 availability auto-detection via HTTP marker file served alongside wasm.
				(async () => {
					const ic3Radio = document.querySelector('input[name="hwcbmc-method"][value="ic3"]');
					if (!ic3Radio) return;
					try {
						const base = (window.__siteBaseUrl || '');
						const url = `${base}/hwcbmc_build/ic3_enabled.txt`;
						const resp = await fetch(url, { method: 'GET', cache: 'no-store' });
						if (resp.ok) {
							ic3Radio.disabled = false;
							const label = ic3Radio.closest('label');
							if (label) label.title = 'IC3 engine available in this build.';
							log('[init] IC3 support detected (ic3_enabled.txt reachable).');
						} else {
							ic3Radio.disabled = true;
							const label = ic3Radio.closest('label');
							if (label) label.title = 'IC3 engine not linked (rebuild with HWCBMC_WASM_ENABLE_IC3=1).';
							log('[init] IC3 marker not found (HTTP ' + resp.status + '); IC3 disabled.');
						}
					} catch (e) {
						ic3Radio.disabled = true;
						const label = ic3Radio.closest('label');
						if (label) label.title = 'IC3 detection error; see console.';
						log('[init] IC3 detection error: ' + e.message);
					}
				})();
		} catch (e) {
			setStatus('Failed to initialize HW-CBMC: ' + e.message);
			log('ERROR: ' + e.message);
		}
	}

	function inferExtFromContentOrName(name) {
		if (name && /\.(v|sv|svh)$/i.test(name)) return 'v';
		if (name && /\.(vhd|vhdl)$/i.test(name)) return 'vhd';
		return 'v';
	}

	function collectCLIArgs(designFile) {
		const args = [designFile];

		const boundEl = document.getElementById('hwcbmc-bound');
		const topEl = document.getElementById('hwcbmc-top');
		const vEl = document.getElementById('hwcbmc-verbosity');

		const bound = boundEl && boundEl.value ? parseInt(boundEl.value, 10) : 1;
		if (bound > 0) {
			args.push('--bound', String(bound));
		}

		if (topEl && topEl.value.trim()) {
			args.push('--top', topEl.value.trim());
		}


		// Method
		const method = (document.querySelector('input[name="hwcbmc-method"]:checked') || {}).value || 'bmc';
		if (method === 'k-induction') args.push('--k-induction');
		else if (method === 'bdd') args.push('--bdd');
		else if (method === 'ic3') args.push('--ic3');
		else if (method === 'random-traces') args.push('--random-traces');
		else if (method === 'random-trace') args.push('--random-trace');
		else if (method === 'random-waveform') args.push('--random-waveform');

		// Randomization params (apply to random-* methods)
		const tracesEl = document.getElementById('hwcbmc-rand-traces');
		const seedEl = document.getElementById('hwcbmc-rand-seed');
		const stepsEl = document.getElementById('hwcbmc-trace-steps');
		const traces = tracesEl && tracesEl.value ? parseInt(tracesEl.value, 10) : 1;
		const rseed = seedEl && seedEl.value ? parseInt(seedEl.value, 10) : 0;
		const steps = stepsEl && stepsEl.value ? parseInt(stepsEl.value, 10) : 0;
		if (method === 'random-traces' && traces > 0) {
			args.push('--traces', String(traces));
		}
		if ((method || '').startsWith('random-')) {
			if (rseed > 0) args.push('--random-seed', String(rseed));
			if (steps > 0) args.push('--trace-steps', String(steps));
		}

		// Traces / waveforms
		if (document.getElementById('hwcbmc-trace')?.checked) {
			args.push('--trace');
		}
		if (document.getElementById('hwcbmc-waveform')?.checked) {
			args.push('--waveform');
		}
		if (document.getElementById('hwcbmc-vcd')?.checked) {
			const vcdName = (document.getElementById('hwcbmc-vcd-file')?.value || 'trace.vcd').trim() || 'trace.vcd';
			args.push('--vcd', vcdName);
		}
		if (document.getElementById('hwcbmc-numbered-trace')?.checked) {
			args.push('--numbered-trace');
		}
		if (document.getElementById('hwcbmc-show-props')?.checked) {
			args.push('--show-properties');
		}
		const jsonResult = document.getElementById('hwcbmc-json-result')?.value?.trim();
		if (jsonResult) args.push('--json-result', jsonResult);
		const jsonProps = document.getElementById('hwcbmc-json-props')?.value?.trim();
		if (jsonProps) args.push('--json-properties', jsonProps);
		// Properties
		const pexpr = document.getElementById('hwcbmc-prop-expr')?.value?.trim();
		if (pexpr) args.push('-p', pexpr);
		const pid = document.getElementById('hwcbmc-prop-id')?.value?.trim();
		if (pid) args.push('--property', pid);

		// Liveness
		if (document.getElementById('hwcbmc-l2s')?.checked) {
			args.push('--liveness-to-safety');
		}
		if (document.getElementById('hwcbmc-buechi')?.checked) {
			args.push('--buechi');
		}

		// Verilog frontend toggles
		if (document.getElementById('hwcbmc-systemverilog')?.checked) {
			args.push('--systemverilog');
		}
		if (document.getElementById('hwcbmc-ignore-initial')?.checked) {
			args.push('--ignore-initial');
		}
		if (document.getElementById('hwcbmc-initial-zero')?.checked) {
			args.push('--initial-zero');
		}
		// Include paths (-I) and defines (-D)
		const incPathsRaw = document.getElementById('hwcbmc-incpaths')?.value || '';
		incPathsRaw.split(/[\n,;]+/).map(s => s.trim()).filter(Boolean).forEach(p => {
			args.push('-I', p);
		});
		const definesRaw = document.getElementById('hwcbmc-defines')?.value || '';
		definesRaw.split(/[\n,;]+/).map(s => s.trim()).filter(Boolean).forEach(d => {
			args.push('-D', d);
		});
		const resetExpr = document.getElementById('hwcbmc-reset')?.value?.trim();
		if (resetExpr) args.push('--reset', resetExpr);

		// Debug output
		if (document.getElementById('hwcbmc-show-netlist')?.checked) {
			args.push('--show-netlist');
		}
		if (document.getElementById('hwcbmc-show-formula')?.checked) {
			args.push('--show-formula');
		}
		if (document.getElementById('hwcbmc-show-trans')?.checked) {
			args.push('--show-trans');
		}
		if (document.getElementById('hwcbmc-preprocess')?.checked) args.push('--preprocess');
		if (document.getElementById('hwcbmc-show-parse')?.checked) args.push('--show-parse');
		if (document.getElementById('hwcbmc-show-modules')?.checked) args.push('--show-modules');
		if (document.getElementById('hwcbmc-show-hierarchy')?.checked) args.push('--show-module-hierarchy');
		if (document.getElementById('hwcbmc-show-varmap')?.checked) args.push('--show-varmap');
		if (document.getElementById('hwcbmc-show-ldg')?.checked) args.push('--show-ldg');
		if (document.getElementById('hwcbmc-smv-netlist')?.checked) args.push('--smv-netlist');
		if (document.getElementById('hwcbmc-dot-netlist')?.checked) args.push('--dot-netlist');
		if (document.getElementById('hwcbmc-smv-word-level')?.checked) args.push('--smv-word-level');
		const outfile = document.getElementById('hwcbmc-outfile')?.value?.trim();
		if (outfile) args.push('--outfile', outfile);

		// Solver / formula output
		if (document.getElementById('hwcbmc-aig')?.checked) args.push('--aig');
		if (document.getElementById('hwcbmc-dimacs')?.checked) args.push('--dimacs');
		if (document.getElementById('hwcbmc-smt2')?.checked) args.push('--smt2');

		// Advanced: neural liveness / ranking function
		if (document.getElementById('hwcbmc-neural')?.checked) {
			args.push('--neural-liveness');
			const engine = document.getElementById('hwcbmc-neural-engine')?.value?.trim();
			if (engine) args.push('--neural-engine', engine);
		}
		if (document.getElementById('hwcbmc-ranking')?.checked) {
			const rfile = (document.getElementById('hwcbmc-ranking-file')?.value || 'ranking.fun').trim() || 'ranking.fun';
			const rtext = document.getElementById('hwcbmc-ranking-text')?.value || '';
			if (rtext.trim()) {
				try { wrapper.writeFile(rfile, rtext); } catch (e) { /* ignore */ }
			}
			args.push('--ranking-function', rfile);
			const rprop = document.getElementById('hwcbmc-ranking-prop')?.value?.trim();
			if (rprop) args.push('--property', rprop);
		}

		if (vEl && vEl.value !== '') {
			args.push('--verbosity', String(parseInt(vEl.value, 10) || 5));
		}

		const extra = document.getElementById('hwcbmc-extra');
		if (extra && extra.value.trim()) {
			// naive split on spaces; advanced users can still quote things
			extra.value.trim().split(/\s+/).forEach((tok) => args.push(tok));
		}

		return args;
	}

	function mkdirp(absPath) {
		if (!wrapper || !wrapper.ready) throw new Error('module not ready');
		const FS = wrapper.module.FS;
		const parts = absPath.split('/').filter(Boolean);
		let cur = '';
		for (let i = 0; i < parts.length - 1; i++) {
			cur += '/' + parts[i];
			try { FS.mkdir(cur); } catch (e) { /* exists */ }
		}
	}

	async function fetchAndWriteAbsolute(url, absPath) {
		const resp = await fetch(url, { cache: 'no-store' });
		if (!resp.ok) throw new Error(`Fetch failed ${resp.status}: ${url}`);
		const text = await resp.text();
		mkdirp(absPath);
		wrapper.writeFile(absPath, text);
		return absPath;
	}

	function writeDesignToFS(fileNameHint) {
		const src = getEditorSource();
		if (!src.trim()) {
			throw new Error('No design source provided. Paste code or upload a file.');
		}

		const ext = inferExtFromContentOrName(fileNameHint);
		const fname = ext === 'vhd' ? 'design.vhd' : 'design.v';
		wrapper.writeFile(fname, src);
		return fname;
	}

	async function runEBMC() {
		await ensureInit();
		if (!wrapper || !wrapper.ready) return;

		setStatus('Running EBMC…');
		setOutput('');

		const fileLabel = document.getElementById('hwcbmc-file-name');
		const nameHint = fileLabel && fileLabel.dataset?.filename;

		let designFile;
		try {
			designFile = writeDesignToFS(nameHint || 'design.v');
		} catch (e) {
			log('ERROR: ' + e.message);
			setStatus('Error: ' + e.message);
			return;
		}

		const argv = collectCLIArgs(designFile);
		log('> ebmc ' + argv.map((a) => (a.includes(' ') ? '"' + a + '"' : a)).join(' '));

		const res = wrapper.execute(argv);

		if (res.stdout) { log(res.stdout); }
		if (res.stderr) { log(res.stderr); }
		const combined = [res.stdout, res.stderr].filter(Boolean).join('\n');
		if (combined) setOutput(combined);

		setStatus(res.success ? 'EBMC finished (exit 0).' : 'EBMC finished with errors (exit ' + res.exitCode + ').');
	}

	async function showHelp() {
		await ensureInit();
		if (!wrapper || !wrapper.ready) return;

		log('> ebmc --help');
		const res = wrapper.execute(['--help']);
		if (res.stdout) log(res.stdout);
		if (res.stderr) log(res.stderr);
	}

	function wireEvents() {
		const upload = document.getElementById('hwcbmc-file');
		const fileLabel = document.getElementById('hwcbmc-file-name');

		// IC3 is conditionally enabled post-initialization; leave temporary disabled state until detection runs.
		const ic3Radio = document.querySelector('input[name="hwcbmc-method"][value="ic3"]');
		if (ic3Radio) {
			ic3Radio.disabled = true; // will be re-enabled if ic3_enabled.txt is found after init
			const label = ic3Radio.closest('label');
			if (label) label.title = 'Detecting IC3 availability…';
		}

		if (upload) {
			upload.addEventListener('change', (e) => {
				const file = e.target.files[0];
				if (!file) return;
				const reader = new FileReader();
				reader.onload = (ev) => {
					const text = ev.target.result;
					setEditorSource(text);
					if (fileLabel) {
						fileLabel.textContent = 'Loaded: ' + file.name;
						fileLabel.dataset.filename = file.name;
					}
					log('Loaded design: ' + file.name);
				};
				reader.readAsText(file);
			});
		}

		const runBtn = document.getElementById('hwcbmc-run');
		if (runBtn) runBtn.addEventListener('click', () => { runEBMC(); });

		const helpBtn = document.getElementById('hwcbmc-show-help');
		if (helpBtn) helpBtn.addEventListener('click', () => { showHelp(); });

		const quickBtn = document.getElementById('hwcbmc-quick-test');
		if (quickBtn) quickBtn.addEventListener('click', async () => {
			await ensureInit();
			if (!wrapper || !wrapper.ready) return;
			try {
				setStatus('Running EBMC quick test…');
				setOutput('');
				// Prefer whatever is in the main editor; if empty, fetch the example, populate editor, then run.
				let src = getEditorSource();
				const fileLabel = document.getElementById('hwcbmc-file-name');
				if (!src.trim()) {
					const base = (window.__siteBaseUrl || '');
					const url = `${base}/examples/formal-verification/shift-register/sr.sv`;
					const resp = await fetch(url, { cache: 'no-store' });
					if (!resp.ok) throw new Error(`HTTP ${resp.status}`);
					src = await resp.text();
					setEditorSource(src);
					if (fileLabel) {
						fileLabel.textContent = 'Loaded example: sr.sv';
						fileLabel.dataset.filename = 'sr.sv';
					}
					log('Loaded example design for quick test: sr.sv');
				}
				// Write the current editor content into a consistent filename used by the command
				const designPath = 'design.v';
				wrapper.writeFile(designPath, src);
				const argv = ['--systemverilog', designPath, '--reset', '~rstn'];
				log('> ebmc ' + argv.join(' '));
				const res = wrapper.execute(argv);
				if (res.stdout) log(res.stdout);
				if (res.stderr) log(res.stderr);
				const combined = [res.stdout, res.stderr].filter(Boolean).join('\n');
				if (combined) setOutput(combined);
				setStatus(res.success ? 'EBMC quick test finished (exit 0).' : 'EBMC quick test finished with errors (exit ' + res.exitCode + ').');
			} catch (e) {
				log('ERROR: ' + e.message);
				setStatus('Quick test error: ' + e.message);
			}
		});

		const copyBtn = document.getElementById('hwcbmc-copy-output');
		if (copyBtn) copyBtn.addEventListener('click', async () => {
			try {
				await navigator.clipboard.writeText(outBuffer || '');
				log('[ui] Results copied to clipboard.');
			} catch (e) {
				log('ERROR copying results: ' + e.message);
			}
		});

		const clearOutBtn = document.getElementById('hwcbmc-clear-output');
		if (clearOutBtn) clearOutBtn.addEventListener('click', () => {
			setOutput('');
		});

		const loadExampleBtn = document.getElementById('hwcbmc-load-example');
		if (loadExampleBtn) loadExampleBtn.addEventListener('click', async () => {
			try {
				const base = (window.__siteBaseUrl || '');
				const url = `${base}/examples/formal-verification/shift-register/sr.sv`;
				const resp = await fetch(url);
				if (!resp.ok) throw new Error(`HTTP ${resp.status}`);
				const text = await resp.text();
				setEditorSource(text);
				const fileLabel = document.getElementById('hwcbmc-file-name');
				if (fileLabel) {
					fileLabel.textContent = 'Loaded example: sr.sv';
					fileLabel.dataset.filename = 'sr.sv';
				}
				log('Loaded example design: sr.sv');
			} catch (e) {
				log('ERROR loading example: ' + e.message);
			}
		});

		const clearBtn = document.getElementById('hwcbmc-clear');
		if (clearBtn) clearBtn.addEventListener('click', () => {
			logBuffer = '';
			const logEl = document.getElementById('hwcbmc-log');
			if (logEl) logEl.textContent = '';
		});

		const dlLogBtn = document.getElementById('hwcbmc-download-log');
		if (dlLogBtn) dlLogBtn.addEventListener('click', () => {
			const blob = new Blob([logBuffer], { type: 'text/plain' });
			const url = URL.createObjectURL(blob);
			const a = document.createElement('a');
			a.href = url;
			a.download = 'hwcbmc_log.txt';
			a.click();
			URL.revokeObjectURL(url);
		});

		const listBtn = document.getElementById('hwcbmc-list');
		if (listBtn) listBtn.addEventListener('click', async () => {
			await ensureInit();
			if (!wrapper || !wrapper.ready) return;
			try {
				const files = wrapper.listFiles('/');
				const el = document.getElementById('hwcbmc-files');
				if (el) el.textContent = files.join('\n');
			} catch (e) {
				log('ERROR: ' + e.message);
			}
		});

		const dlBtn = document.getElementById('hwcbmc-download');
		if (dlBtn) dlBtn.addEventListener('click', async () => {
			await ensureInit();
			if (!wrapper || !wrapper.ready) return;
			const nameEl = document.getElementById('hwcbmc-artifact');
			const name = nameEl && nameEl.value.trim();
			if (!name) {
				log('Please enter a filename to download (e.g., trace.vcd or result.json).');
				return;
			}
			try {
				const data = wrapper.readFile(name);
				const bytes = data instanceof Uint8Array ? data : new TextEncoder().encode(String(data));
				const blob = new Blob([bytes], { type: 'application/octet-stream' });
				const url = URL.createObjectURL(blob);
				const a = document.createElement('a');
				a.href = url;
				a.download = name;
				a.click();
				URL.revokeObjectURL(url);
				log('Downloaded artifact: ' + name);
			} catch (e) {
				log('ERROR: ' + e.message);
			}
		});
	}

	window.addEventListener('load', () => {
		setStatus('Loading HW-CBMC module…');
		wireEvents();
		ensureInit();
	});
})();
