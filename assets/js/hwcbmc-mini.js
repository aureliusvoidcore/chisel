// Minimal EBMC runner for the Shift registers/pipelines page
// Depends on hwcbmc_build/hwcbmc.js and hwcbmc_build/hwcbmc-wrapper.js being loaded first.

(function () {
  const $ = (sel) => document.querySelector(sel);
  const outputEl = $('#sr-output'); // optional console area if present

  const wrapper = new HWCBMCWrapper();
  let initialized = false;

  function appendOutput(line) {
    if (outputEl) {
      outputEl.textContent += (outputEl.textContent ? '\n' : '') + line;
      outputEl.scrollTop = outputEl.scrollHeight;
    } else {
      console.log(line);
    }
  }

  function clearOutput() {
    if (outputEl) outputEl.textContent = '';
  }

  async function initWasm() {
    if (initialized) return;
    try {
      await wrapper.initialize({
        print: (t) => appendOutput(String(t)),
        printErr: (t) => appendOutput(String(t)),
        noInitialRun: true,
        locateFile: (path, prefix) => prefix + path
      });
      initialized = true;
    } catch (e) {
      appendOutput('Initialization failed: ' + String(e));
      throw e;
    }
  }

  function getEditorSource() {
    // Prefer CodeMirror instance created by editorify
    const cmEl = document.querySelector('.editorify-wrap .CodeMirror');
    if (cmEl && cmEl.CodeMirror && typeof cmEl.CodeMirror.getValue === 'function') {
      return cmEl.CodeMirror.getValue();
    }
    // Fallback to raw code block content
    const codeEl = document.querySelector('pre code.language-systemverilog, pre code.language-verilog, pre code');
    if (codeEl) return codeEl.textContent || '';
    return '';
  }

  function buildArgv(extra) {
    const argv = ['--systemverilog', 'design.v', '--reset', '~rstn'];
    if (extra && extra.trim().length > 0) {
      const tokens = extra.match(/(?:\"[^\"]*\"|'[^']*'|\S+)/g) || [];
      argv.push(...tokens.map(s => s.replace(/^['\"]|['\"]$/g, '')));
    }
    return argv;
  }

  async function run(extraArgs) {
    await initWasm();
    clearOutput();
    const src = getEditorSource();
    if (!src || !src.trim()) {
      appendOutput('No source found in the editor.');
      return { success: false, exitCode: -1 };
    }
    try {
      wrapper.writeFile('design.v', src);
    } catch (e) {
      appendOutput('FS error: ' + String(e));
    }
    const argv = buildArgv(String(extraArgs || ''));
    const result = wrapper.execute(argv);
    if (result.stderr) appendOutput(result.stderr);
    if (result.stdout) appendOutput(result.stdout);
    return result;
  }

  // Expose globals so existing buttons can call these
  window.runShiftRegisterEBMC = run;
  window.clearShiftRegisterOutput = clearOutput;

  // If specific controls exist on the page, wire them (optional)
  window.addEventListener('load', () => {
    const runBtn = $('#sr-run');
    const clearBtn = $('#sr-clear');
    const extraArgsEl = $('#sr-extra-args');
    if (runBtn) runBtn.addEventListener('click', () => run(extraArgsEl ? extraArgsEl.value : ''));
    if (clearBtn) clearBtn.addEventListener('click', () => clearOutput());
  });
})();
