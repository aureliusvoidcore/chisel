(function(){
  const UI_VER = 'cvc5-ui/2025-10-28-1';
  try { console.log('[cvc5-ui] loaded', UI_VER); } catch {}
  const ui = {
    input: null,
    output: null,
    errors: null,
    stats: null,
    runBtn: null,
    stopBtn: null,
    loadBtn: null,
    options: {},
    status: null,
    loader: null,
  };

  let ModuleFactory = null;
  let busy = false;

  function qs(id){ return document.getElementById(id); }
  function setStatus(msg){ if (ui.status) ui.status.textContent = msg || ''; }
  function appendOut(el, text){ el.textContent += text + "\n"; }
  function clear(el){ el.textContent = ''; }

  function bytesToString(bytes){
    if (!bytes || !bytes.length) return '';
    let s = '';
    const CHUNK = 8192;
    for (let i = 0; i < bytes.length; i += CHUNK) {
      s += String.fromCharCode.apply(null, bytes.slice(i, i + CHUNK));
    }
    return s;
  }

  async function loadScript(src){
    return new Promise((resolve, reject)=>{
      const s = document.createElement('script');
      s.src = src; s.async = true;
      s.onload = ()=> resolve();
      s.onerror = ()=> reject(new Error('Failed to load ' + src));
      document.head.appendChild(s);
    });
  }

  async function ensureCVC5Factory(){
    if (ModuleFactory) return ModuleFactory;
    const path = (window.__CVC5_JS_PATH__) || (window.__baseurl__ || '') + '/assets/cvc5/cvc5.js';
    try {
      if (!window.__CVC5_OUT) window.__CVC5_OUT = [];
      if (!window.__CVC5_ERR) window.__CVC5_ERR = [];
      if (typeof window.Module === 'undefined') {
        window.Module = {
          noInitialRun: true,
          print: (txt)=> { (window.__CVC5_OUT || []).push(String(txt)); },
          printErr: (txt)=> { (window.__CVC5_ERR || []).push(String(txt)); },
          locateFile: (p)=> {
            if (p.endsWith('.wasm')) return (window.__CVC5_WASM_PATH__) || (window.__baseurl__ || '') + '/assets/cvc5/cvc5.wasm';
            return p;
          }
        };
      }
      await loadScript(path);
      // MODULARIZE=true -> factory function
      if (typeof Module === 'function') { ModuleFactory = Module; ModuleFactory.__kind='factory'; return ModuleFactory; }
      // Emscripten Promise export
      if (Module && typeof Module === 'object' && typeof Module.then === 'function') {
        const f = () => Module; f.__kind = 'promise'; ModuleFactory = f; return ModuleFactory;
      }
      // Global Module object (legacy)
      if (Module && typeof Module === 'object') {
        const f = () => (Module.ready && typeof Module.ready.then === 'function') ? Module.ready.then(()=>Module) : Promise.resolve(Module);
        f.__kind = 'object'; ModuleFactory = f; return ModuleFactory;
      }
    } catch (e){ console.warn(e); }
    throw new Error('cvc5.js not found. Place cvc5.js and cvc5.wasm under assets/cvc5/.');
  }

  function buildArgs(opts){
    const args = [];
    // Do NOT force --interactive=false; some builds suppress output.
    if (opts.lang && opts.lang !== 'auto') args.push('--lang=' + opts.lang);
    if (opts.logic) args.push('--logic=' + opts.logic);
    const isSyGuS = (opts.lang === 'sygus2');
    if (!isSyGuS) {
      if (opts.models) args.push('--produce-models');
      if (opts.unsat) args.push('--produce-unsat-cores');
      if (opts.incr) args.push('--incremental');
      if (opts.bvSat) args.push('--bv-sat-solver=' + opts.bvSat);
      if (opts.strExp) args.push('--strings-exp');
    } else {
      if (opts.sygusEnum) args.push('--sygus-enum');
    }
    if (opts.tlimit && opts.tlimit > 0) args.push('--tlimit-per=' + parseInt(opts.tlimit,10));
    if (opts.seed) args.push('--seed=' + parseInt(opts.seed,10));
    if (opts.stats) args.push('--stats');
    // Increase CVC5 internal verbosity when requested
    if (opts.verbose) args.push('--verbosity=4');
    if (opts.extra) {
      try {
        const extra = opts.extra.split(/\s+/).filter(Boolean);
        args.push(...extra);
      } catch {}
    }
    return args;
  }

  async function runCVC5(inputText, opts){
    const start = performance.now();
    clear(ui.output); clear(ui.stats);
    setStatus('Preparing...');
  // Supports modularized factory and legacy global Module

  const out = [];
  const err = [];
  const outChars = [];
  const errChars = [];
    window.__CVC5_OUT = out;
    window.__CVC5_ERR = err;

  // Feed stdin as a byte stream
    const enc = new TextEncoder();
    const inBytes = enc.encode(inputText.endsWith('\n') ? inputText : (inputText + '\n'));
    let inIdx = 0;
    function stdin(){
      if (inIdx >= inBytes.length) return null;
      return inBytes[inIdx++];
    }

  const args = buildArgs(opts);
    args.push('-');
  const kind = (opts && opts.lang === 'sygus2') ? 'sygus' : 'smt';
  try { console.log(`[cvc5] start kind=${kind} args=${args.join(' ')}`); } catch {}

    function locateFile(p){
      if (p.endsWith('.wasm')) return (window.__CVC5_WASM_PATH__) || (window.__baseurl__ || '') + '/assets/cvc5/cvc5.wasm';
      return p;
    }

  // Filter banner/prompts locally for Output only

    function stripBanner(text){
      if (!text) return '';
      const lines = String(text).split(/\r?\n/);
      if (!/^cvc5\b/.test(lines[0] || '')) return text; // no banner detected
      // find end of banner (line ending with 'warranty information.'), then skip following blank lines
      let end = -1;
      for (let i=0;i<lines.length;i++){
        if (/warranty information\.$/i.test(lines[i])) { end = i; break; }
      }
      if (end === -1) return text;
      let j = end + 1;
      while (j < lines.length && lines[j].trim() === '') j++;
      return lines.slice(j).join('\n');
    }

    function stripPrompts(text){
      if (!text) return '';
      // Remove repeated 'cvc5>' tokens and standalone prompt lines
      const lines = String(text).split(/\r?\n/).filter(l => l.trim() !== 'cvc5>');
      return lines.map(l => l.replace(/^(?:cvc5>\s*)+/, '').replace(/(?:\s+cvc5>\s*)+/g, ' ')).join('\n');
    }

    function isErrorLine(l){ return /^(\(error\b|Parse Error:|Error:|\[abort\]|fatal|exception)/i.test(l || ''); }

    function finish(code){
      const dt = (performance.now() - start).toFixed(1);
      const rawOut = (outChars.length ? bytesToString(outChars) : out.join('\n'));
      const outText = stripPrompts(stripBanner(rawOut));
      const errRaw = (errChars.length ? bytesToString(errChars) : err.join('\n'));
      const errText = errRaw;
      if (outText) appendOut(ui.output, outText);
      const errLines = errText ? errText.split(/\r?\n/).filter(isErrorLine) : [];
      const statLines = (opts && opts.stats && errText) ? errText.split(/\r?\n/).filter(l=> !isErrorLine(l)) : [];
      const outErrFromStdout = outText ? outText.split(/\r?\n/).filter(isErrorLine) : [];
      const allErrLines = errLines.concat(outErrFromStdout);
      if (allErrLines.length) appendOut(ui.errors || ui.output, allErrLines.join('\n'));
      if (opts && opts.stats && ui.stats && statLines.length) appendOut(ui.stats, statLines.join('\n'));
      ui.stats.textContent = ['Exit code: ' + code, 'Time: ' + dt + ' ms'].join('\n');
      try {
        if (opts && opts.verbose){
          const lines = [];
          lines.push(`[cvc5] ${kind.toUpperCase()} run`);
          lines.push('args: ' + args.join(' '));
          lines.push('input bytes: ' + inBytes.length);
          lines.push('time ms: ' + dt);
          lines.push('exit code: ' + code);
          lines.push('stdout bytes: ' + rawOut.length);
          lines.push('stderr bytes: ' + errText.length);
          if (outText) { lines.push('--- stdout ---'); lines.push(outText); }
          if (errText) { lines.push('--- stderr ---'); lines.push(errText); }
          lines.push('--- end ---');
          console.log(lines.join('\n'));
        }
        // Always print a one-line summary for quick inspection
        console.log(`[cvc5] done kind=${kind} code=${code} ms=${dt} outBytes=${rawOut.length} errBytes=${errText.length}`);
        // Duplicate outputs to console for easier debugging regardless of language
        if (args && args.length) console.log('[cvc5] args ' + args.join(' '));
        if (outText) console.log('[cvc5] stdout\n' + outText);
        if (errText) console.log('[cvc5] stderr\n' + errText);
      } catch {}
      if (code !== 0 || allErrLines.length) setStatus('Error'); else setStatus('Ready');
      try { if (ui.errors) ui.errors.scrollTop = ui.errors.scrollHeight; } catch {}
      busy = false;
      ui.runBtn.disabled = false;
      return { code, out, err, dt, args };
    }

  const factory = await ensureCVC5Factory();
    setStatus('Solving...');

    return new Promise((resolve, reject)=>{
      const baseurl = (window.__baseurl__ || '');
      const srcBase = (window.__CVC5_JS_PATH__) || (baseurl + '/assets/cvc5/cvc5.js');
      let resolved = false;
      const done = (code)=>{
        if (resolved) return;
        resolved = true;
        resolve(finish(code ?? 0));
      };
      if (factory && factory.__kind === 'factory') {
        try {
          factory({
            noInitialRun: false,
            noExitRuntime: false,
            arguments: args,
            print: (txt)=> out.push(String(txt)),
            printErr: (txt)=> err.push(String(txt)),
            stdin,
            stdout: (ch)=> outChars.push(ch & 0xff),
            stderr: (ch)=> errChars.push(ch & 0xff),
            locateFile,
            onExit: (code)=> done(code),
            quit: (status /*, toThrow*/)=>{ done(status ?? 0); },
            onAbort: (what)=>{ appendOut(ui.output, '[abort] ' + what); done(-1); },
          }).catch((e)=>{ appendOut(ui.output, 'Exception: ' + e.message); resolve(finish(-1)); });
        } catch(e){ appendOut(ui.output, 'Exception: ' + e.message); resolve(finish(-1)); }
      } else {
        try {
          window.Module = {
            noInitialRun: false,
            noExitRuntime: false,
            arguments: args,
            print: (txt)=> out.push(String(txt)),
            printErr: (txt)=> err.push(String(txt)),
            stdin,
            stdout: (ch)=> outChars.push(ch & 0xff),
            stderr: (ch)=> errChars.push(ch & 0xff),
            locateFile,
            onExit: (code)=> done(code),
            quit: (status /*, toThrow*/)=>{ done(status ?? 0); },
            onAbort: (what)=>{ appendOut(ui.output, '[abort] ' + what); done(-1); },
          };
          const s = document.createElement('script');
          s.src = srcBase + (srcBase.includes('?') ? '&' : '?') + 'run=' + Date.now();
          s.async = true;
          s.onerror = ()=>{ appendOut(ui.output, 'Failed to load cvc5.js'); done(-1); };
          document.head.appendChild(s);
        } catch(e){ appendOut(ui.output, 'Exception: ' + e.message); resolve(finish(-1)); }
      }
      const tEl = qs('cvc5-timeout');
      const tVal = (tEl && parseInt(tEl.value, 10)) || 0;
      if (tVal > 0) {
        setTimeout(()=>{
          if (ui.status && ui.status.textContent && ui.status.textContent.includes('Solving')) {
            const partialErr = (errChars.length ? bytesToString(errChars) : err.join('\n'));
            appendOut(ui.errors || ui.output, `[timeout] Solver did not finish within ${tVal}ms` + (partialErr? ('\n' + partialErr) : ''));
            done(-1);
          }
        }, tVal);
      }
    });
  }

  function getOptions(){
    return {
      lang: qs('cvc5-lang').value, // auto|smtlib2.6|sygus2
      logic: qs('cvc5-logic').value.trim(),
      models: qs('cvc5-models').checked,
      unsat: qs('cvc5-unsat').checked,
      incr: qs('cvc5-incremental').checked,
      tlimit: parseInt(qs('cvc5-timeout').value, 10) || 0,
      seed: parseInt(qs('cvc5-seed').value, 10) || 0,
      strExp: qs('cvc5-strings-exp').checked,
      bvSat: qs('cvc5-bv-sat').value,
      verbose: qs('cvc5-verbose').checked,
      sygusEnum: (qs('cvc5-sygus-enum') && qs('cvc5-sygus-enum').checked) || false,
      stats: (function(){ const x = document.getElementById('cvc5-stats-flag'); return !!(x && x.checked); })(),
      extra: qs('cvc5-extra').value.trim(),
    };
  }

  function loadExample(kind){
    const SMT_EX = `(set-logic QF_BV)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(assert (= (bvadd a b) #x2a))
(check-sat)
(get-model)`;
  const SY_EX = `; The printed output for this example should be equivalent to:
; (
;   (define-fun inv-f ((x Int)) Bool (not (>= x 11)))
; )

(set-logic LIA)
(synth-fun inv-f ((x Int)) Bool)
(define-fun pre-f ((x Int)) Bool (= x 0))
(define-fun trans-f ((x Int) (xp Int)) Bool (ite (< x 10) (= xp (+ x 1)) (= xp x)))
(define-fun post-f ((x Int)) Bool (<= x 10))
(inv-constraint inv-f pre-f trans-f post-f)
(check-synth)`;
  const SR_EX = `(set-logic BV)

(synth-fun inv ((sr0 (_ BitVec 1)) (sr1 (_ BitVec 1)) (past_sr0 (_ BitVec 1)) (past_sr1 (_ BitVec 1)) (past_en (_ BitVec 1)) (past_din (_ BitVec 1))) Bool
  ((Start Bool) (Term (_ BitVec 1)))
  ((Start Bool (true false (and Start Start) (or Start Start) (not Start) (= Term Term)))
   (Term (_ BitVec 1) (sr0 sr1 past_sr0 past_sr1 past_en past_din #b0 #b1))))

(define-fun pre ((sr0 (_ BitVec 1)) (sr1 (_ BitVec 1)) (past_sr0 (_ BitVec 1)) (past_sr1 (_ BitVec 1)) (past_en (_ BitVec 1)) (past_din (_ BitVec 1))) Bool
  (and (= sr0 #b0) (= sr1 #b0) (= past_sr0 #b0) (= past_sr1 #b0) (= past_en #b0) (= past_din #b0)))

(define-fun trans ((sr0 (_ BitVec 1)) (sr1 (_ BitVec 1)) (past_sr0 (_ BitVec 1)) (past_sr1 (_ BitVec 1)) (past_en (_ BitVec 1)) (past_din (_ BitVec 1))
                   (sr0_next (_ BitVec 1)) (sr1_next (_ BitVec 1)) (past_sr0_next (_ BitVec 1)) (past_sr1_next (_ BitVec 1)) (past_en_next (_ BitVec 1)) (past_din_next (_ BitVec 1))) Bool
  (or
    ;; rstn=0, en=0, din=0
    (and (= past_en_next #b0) (= past_din_next #b0) (= past_sr0_next #b0) (= past_sr1_next #b0) (= sr0_next #b0) (= sr1_next #b0))
    ;; rstn=0, en=0, din=1
    (and (= past_en_next #b0) (= past_din_next #b0) (= past_sr0_next #b0) (= past_sr1_next #b0) (= sr0_next #b0) (= sr1_next #b0))
    ;; rstn=0, en=1, din=0
    (and (= past_en_next #b0) (= past_din_next #b0) (= past_sr0_next #b0) (= past_sr1_next #b0) (= sr0_next #b0) (= sr1_next #b0))
    ;; rstn=0, en=1, din=1
    (and (= past_en_next #b0) (= past_din_next #b0) (= past_sr0_next #b0) (= past_sr1_next #b0) (= sr0_next #b0) (= sr1_next #b0))
    ;; rstn=1, en=0, din=0
    (and (= past_en_next #b0) (= past_din_next #b0) (= past_sr0_next sr0) (= past_sr1_next sr1) (= sr0_next sr0) (= sr1_next sr1))
    ;; rstn=1, en=0, din=1
    (and (= past_en_next #b0) (= past_din_next #b1) (= past_sr0_next sr0) (= past_sr1_next sr1) (= sr0_next sr0) (= sr1_next sr1))
    ;; rstn=1, en=1, din=0
    (and (= past_en_next #b1) (= past_din_next #b0) (= past_sr0_next sr0) (= past_sr1_next sr1) (= sr0_next sr1) (= sr1_next #b0))
    ;; rstn=1, en=1, din=1
    (and (= past_en_next #b1) (= past_din_next #b1) (= past_sr0_next sr0) (= past_sr1_next sr1) (= sr0_next sr1) (= sr1_next #b1))))

(define-fun post ((sr0 (_ BitVec 1)) (sr1 (_ BitVec 1)) (past_sr0 (_ BitVec 1)) (past_sr1 (_ BitVec 1)) (past_en (_ BitVec 1)) (past_din (_ BitVec 1))) Bool
  (and (or (not (= past_en #b1)) (and (= sr1 past_din) (= sr0 past_sr1)))
       (or (not (= past_en #b0)) (and (= sr0 past_sr0) (= sr1 past_sr1)))))

(inv-constraint inv pre trans post)

(check-synth)`;
    if (kind === 'sr') {
      ui.input.value = SR_EX;
      qs('cvc5-lang').value = 'sygus2';
      // Configure options based on args file
      qs('cvc5-verbose').checked = true;
      qs('cvc5-extra').value = '--sygus-enum=smart --sygus-simple-sym-break=agg --sygus-min-grammar --sygus-core-connective --sygus-pbe --sygus-abort-size=1000 --sygus-repair-const --sygus-repair-const-timeout=5000 --sygus-inv-templ=post --sygus-eval-unfold=single-bool --output=sygus --stats --stats-internal';
    } else {
      ui.input.value = (kind === 'sygus') ? SY_EX : SMT_EX;
      if (kind === 'sygus') qs('cvc5-lang').value = 'sygus2';
    }
  }

  function wire(){
    ui.input = qs('cvc5-input');
    ui.output = qs('cvc5-output');
    ui.errors = qs('cvc5-errors');
    ui.stats = qs('cvc5-stats');
    ui.runBtn = qs('cvc5-run');
    ui.stopBtn = qs('cvc5-stop');
    ui.loadBtn = qs('cvc5-load');
    ui.status = qs('cvc5-status');
    function refreshVisibility(){
      const lang = qs('cvc5-lang').value;
      const isSyGuS = (lang === 'sygus2');
      document.querySelectorAll('.only-smt').forEach(el=>{ el.style.display = isSyGuS ? 'none' : ''; });
      document.querySelectorAll('.only-sygus').forEach(el=>{ el.style.display = isSyGuS ? '' : 'none'; });
    }

    qs('cvc5-lang').addEventListener('change', refreshVisibility);
    refreshVisibility();


    try { window.__baseurl__ = document.querySelector('link[rel="icon"]').href.replace(/\/assets.*$/, ''); } catch {}

    ui.runBtn.addEventListener('click', async ()=>{
      if (busy) return; busy = true; ui.runBtn.disabled = true; setStatus('Loading cvc5...');
      const text = ui.input.value;
      const opts = getOptions();
      await runCVC5(text, opts);
    });
    ui.loadBtn.addEventListener('click', ()=>{
      const k = qs('cvc5-example').value;
      loadExample(k);
    });
    const up = qs('cvc5-file');
    up.addEventListener('change', async ()=>{
      const f = up.files && up.files[0]; if (!f) return;
      const text = await f.text(); ui.input.value = text;
    });
    qs('cvc5-dl-out').addEventListener('click', ()=>{
      const blob = new Blob([ui.output.textContent || ''], {type:'text/plain'});
      const a = document.createElement('a'); a.href=URL.createObjectURL(blob); a.download='cvc5-output.txt'; a.click();
    });
  qs('cvc5-clear').addEventListener('click', ()=>{ ui.input.value=''; clear(ui.output); if (ui.errors) clear(ui.errors); clear(ui.stats); });

    setStatus('Ready');
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', wire);
  else wire();
})();
