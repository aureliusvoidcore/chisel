(function(){
  function log(msg){ /* quiet; enable if needed */ }
  function findTargetBlocks(root){
    const selectors = [
      'div.highlight pre code',
      'pre code'
    ];
    const nodes = [];
    selectors.forEach(sel => root.querySelectorAll(sel).forEach(n => nodes.push(n)));
    return nodes;
  }
  function detectLang(codeEl){
    const cls = codeEl.className || '';
    const m = cls.match(/language-([A-Za-z0-9_+-]+)/);
    const lang = (m && m[1] || '').toLowerCase();
    // Normalize some aliases
    if (lang === 'sv' || lang === 'systemverilog' || lang === 'sva' || lang === 'verilog') return 'verilog';
    if (lang === 'smt' || lang === 'smt2' || lang === 'smtlib' || lang === 'sygus') return 'scheme';
    return lang;
  }
  function shouldEnhance(lang){
    const targets = new Set(['verilog','scheme']);
    return targets.has(lang);
  }
  function createToolbar(lang, onReset, onCopy){
    const bar = document.createElement('div');
    bar.className = 'editorify-toolbar';
    const label = document.createElement('span');
    label.className = 'editorify-label';
    label.textContent = lang ? `Editor (${lang})` : 'Editor';
    const btnReset = document.createElement('button');
    btnReset.type = 'button'; btnReset.className = 'editorify-btn'; btnReset.textContent = 'Reset';
    btnReset.addEventListener('click', onReset);
    const btnCopy = document.createElement('button');
    btnCopy.type = 'button'; btnCopy.className = 'editorify-btn'; btnCopy.textContent = 'Copy';
    btnCopy.addEventListener('click', onCopy);
    bar.appendChild(label); bar.appendChild(btnReset); bar.appendChild(btnCopy);
    return bar;
  }
  function enhanceCodeBlock(codeEl){
    if (typeof window.CodeMirror === 'undefined') return; // safety: if codemirror hasn't loaded, do nothing
    const lang = detectLang(codeEl);
    if (!shouldEnhance(lang)) return;
    // Don't enhance if explicitly opted out
    if (codeEl.closest('[data-no-editor]')) return;
    // Don't re-enhance an already enhanced block
    if (codeEl.closest('.editorify-wrap')) return;

    const pre = codeEl.closest('pre') || codeEl.parentElement;
    const wrapper = document.createElement('div');
    wrapper.className = 'editorify-wrap';

    const original = codeEl.textContent; // baseline content
    const ta = document.createElement('textarea');
    ta.value = original;
    ta.setAttribute('aria-label', 'Code editor');

    const toolbar = createToolbar(lang, () => {
      editor.setValue(original);
    }, async () => {
      try { await navigator.clipboard.writeText(editor.getValue()); } catch(e) {}
    });

    // Replace only the code block element (highlight wrapper or the <pre> itself),
    // never an arbitrary parent container to avoid removing surrounding content.
    const container = pre.closest('div.highlight, figure.highlight, pre') || pre;
    container.replaceWith(wrapper);
    wrapper.appendChild(toolbar);
    wrapper.appendChild(ta);

    // Init CodeMirror
    const cmMode = lang || null;
    const editor = CodeMirror.fromTextArea(ta, {
      mode: cmMode,
      lineNumbers: true,
      lineWrapping: true,
      viewportMargin: Infinity,
      theme: 'darcula',
      indentUnit: 2,
      tabSize: 2,
    });
    // Smart size to content while respecting layout
    function autoSize(){
      try{
        const lines = editor.lineCount();
        const lh = editor.defaultTextHeight ? editor.defaultTextHeight() : 18;
        const minPx = 240; // ~13-14 lines default minimum
        const maxPx = Math.min(800, Math.max(minPx, (lines + 2) * lh)); // cap ~45 lines
        editor.setSize('100%', maxPx + 'px');
      }catch(e){ editor.setSize('100%', null); }
      editor.refresh();
    }
    setTimeout(autoSize, 0);
    editor.on('change', autoSize);
    // Refresh on container resize to follow layout
    if ('ResizeObserver' in window){
      const ro = new ResizeObserver(() => editor.refresh());
      ro.observe(wrapper);
    } else {
      window.addEventListener('resize', () => editor.refresh());
    }
  }

  function run(){
    const root = document.querySelector('main.container') || document;
    if (!root) return;
    const blocks = findTargetBlocks(root);
    blocks.forEach(enhanceCodeBlock);
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', run);
  } else {
    run();
  }
})();
