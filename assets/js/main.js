 (function(){
  const doc = document;
  const body = doc.body;
  const prefersReduced = window.matchMedia('(prefers-reduced-motion: reduce)').matches;
  
  // Runtime tunables
  let laserMode = 'sweep';
  let rainbowSpeed = 1.0; // multiplier for rainbow hue rotation
  let activeTab = 'themes';

  // Lights mode: default off; persist in localStorage
  const KEY = 'lights-mode';
  function applyMode(mode){
    body.classList.toggle('lights-on', mode === 'on');
    body.classList.toggle('lights-off', mode !== 'on');
    const btn = doc.getElementById('cp-lights');
    if (btn) btn.setAttribute('aria-pressed', String(mode === 'on'));
  }
  const toggle = doc.getElementById('cp-lights');
  if (toggle){
    toggle.addEventListener('click', function(){
      const next = body.classList.contains('lights-on') ? 'off' : 'on';
      localStorage.setItem(KEY, next);
      applyMode(next);
    });
  }

  // Control Panel wiring
  const CP = {
    theme: doc.getElementById('cp-theme'),
    a1: doc.getElementById('cp-accent1'),
    a2: doc.getElementById('cp-accent2'),
    a3: doc.getElementById('cp-accent3'),
    grid: doc.getElementById('cp-grid'),
    scan: doc.getElementById('cp-scan'),
    laser: doc.getElementById('cp-laser-mode'),
    rainbow: doc.getElementById('cp-rainbow-speed'),
    secLaser: doc.getElementById('cp-section-laser'),
    secRainbow: doc.getElementById('cp-section-rainbow'),
    secDoom: doc.getElementById('cp-section-doom'),
    dInt: doc.getElementById('cp-doom-intensity'),
    dVol: doc.getElementById('cp-doom-volume'),
    dReduced: doc.getElementById('cp-doom-reduced'),
    bgColor: doc.getElementById('cp-bg-color'),
    bgBright: doc.getElementById('cp-bg-brightness'),
    presetBlue: doc.getElementById('cp-preset-blue'),
    presetViolet: doc.getElementById('cp-preset-violet'),
    presetMiami: doc.getElementById('cp-preset-miami'),
    presetAlien: doc.getElementById('cp-preset-alien'),
    presetAlienXmas: doc.getElementById('cp-preset-alien-xmas'),
    presetAmber: doc.getElementById('cp-preset-amber'),
    presetSynth: doc.getElementById('cp-preset-synth'),
    presetRog: doc.getElementById('cp-preset-rog'),
    presetTealPurple: doc.getElementById('cp-preset-tealpurple'),
    reset: doc.getElementById('cp-reset'),
    tabs: Array.from(doc.querySelectorAll('.tab-button')),
    panes: Array.from(doc.querySelectorAll('.tab-pane')),
  };
  const STORE = 'cp-state-v1';
  const TAB_STORE = 'cp-tab-v1';
  function detectTheme(){
    for (const c of body.classList) if (c.startsWith('theme-')) return c.slice(6);
    return 'alien-xmas';
  }
  function state(){
    return {
      theme: detectTheme(),
      a1: getVar('--neon-blue'), a2: getVar('--neon-green'), a3: getVar('--neon-pink'),
      grid: parseInt(getVar('--grid-size') || '40', 10),
      scan: !body.classList.contains('scan-off'),
      laser: laserMode,
      rainbow: rainbowSpeed,
      bg: getVar('--bg-base') || '#05060a',
      bgl: parseInt((getVar('--bg-lighten') || '0%').replace('%',''), 10) || 0,
      dInt: (CP.dInt && CP.dInt.value) || (ultra?'ultra':'normal'),
      dVol: (CP.dVol && parseFloat(CP.dVol.value)) || currentVolume || 0.55,
      dReduced: (CP.dReduced && CP.dReduced.checked) || doomReduced || false
    };
  }
  function load(){
    try { return JSON.parse(localStorage.getItem(STORE) || '{}'); } catch { return {}; }
  }
  function save(s){ localStorage.setItem(STORE, JSON.stringify(s)); }
  function setVar(name, val){ doc.documentElement.style.setProperty(name, val); }
  function getVar(name){ return getComputedStyle(doc.documentElement).getPropertyValue(name).trim(); }
  function applyTheme(theme){
    const classes = ['theme-alien-xmas','theme-neon','theme-matrix','theme-rainbow','theme-laser','theme-amber','theme-synthwave','theme-rog','theme-win98','theme-amiga','theme-mac','theme-doom'];
    for(const c of classes) body.classList.remove(c);
    body.classList.add('theme-' + (theme || 'neon'));
  }
  function setHidden(el, hidden){ if (!el) return; el.classList.toggle('is-hidden', !!hidden); }
  function updateCPVisibility(theme){
    const t = theme || detectTheme();
    // Laser controls only for the Laser theme (not Doom)
    setHidden(CP.secLaser, t !== 'laser');
    setHidden(CP.secRainbow, t !== 'rainbow');
    setHidden(CP.secDoom, t !== 'doom');
  }
  function applyTab(tab){
    activeTab = tab || 'themes';
    for(const b of CP.tabs){
      const sel = (b.dataset.tab === activeTab);
      b.setAttribute('aria-selected', String(sel));
    }
    for(const p of CP.panes){
      const show = (p.dataset.tabPanel === activeTab);
      p.classList.toggle('is-hidden', !show);
      p.setAttribute('aria-hidden', String(!show));
    }
    try{ localStorage.setItem(TAB_STORE, activeTab); } catch{}
  }
  function apply(s){
    // theme
    applyTheme(s.theme);
    if (CP.theme) CP.theme.value = s.theme;
    updateCPVisibility(s.theme);
    // colors
    if (s.a1) setVar('--neon-blue', s.a1);
    if (s.a2) setVar('--neon-green', s.a2);
    if (s.a3) setVar('--neon-pink', s.a3);
    if (CP.a1) CP.a1.value = s.a1 || '#00ffff';
    if (CP.a2) CP.a2.value = s.a2 || '#00ff88';
    if (CP.a3) CP.a3.value = s.a3 || '#ff00ff';
    // grid
    const g = (s.grid && Number.isFinite(s.grid)) ? s.grid : 40;
    setVar('--grid-size', g + 'px');
    if (CP.grid) CP.grid.value = g;
    // scanlines
    body.classList.toggle('scan-off', s.scan === false);
    if (CP.scan) CP.scan.checked = (s.scan !== false);
    // laser mode
    laserMode = s.laser || 'sweep';
    if (CP.laser) CP.laser.value = laserMode;
    // rainbow speed
    rainbowSpeed = (typeof s.rainbow === 'number' && s.rainbow > 0) ? s.rainbow : 1.0;
    if (CP.rainbow) CP.rainbow.value = String(rainbowSpeed);
    // background
    if (s.bg) setVar('--bg-base', s.bg);
    const bgl = (typeof s.bgl === 'number' && s.bgl >= 0) ? s.bgl : 0;
    setVar('--bg-lighten', bgl + '%');
    if (CP.bgColor) CP.bgColor.value = s.bg || '#05060a';
    if (CP.bgBright) CP.bgBright.value = String(bgl);
  }
  // Ensure the Theme select includes Doom and label it as Doom Classic
  if (CP.theme) {
    const opts = Array.from(CP.theme.options || []);
    let doomOpt = opts.find(o => o.value === 'doom');
    if (!doomOpt) {
      doomOpt = doc.createElement('option');
      doomOpt.value = 'doom';
      // Insert near the top, after Neon Cyberpunk
      if (CP.theme.firstElementChild && CP.theme.firstElementChild.value === 'neon') {
        CP.theme.insertBefore(doomOpt, CP.theme.children[1] || null);
      } else {
        CP.theme.insertBefore(doomOpt, CP.theme.firstChild);
      }
    }
    doomOpt.textContent = 'Doom Classic';
  }

  // Default to Alien / Cyberpunk Christmas theme
  function defaultAlienXmasSettings(){
    return { dInt: 'normal', dVol: 0.0, dReduced: true };
  }
  const s0 = Object.assign({ theme: 'alien-xmas', a1:'#4ef3ff', a2:'#00ff88', a3:'#ff3366', grid:40, scan:true, laser:'sweep', rainbow:1.0, bg:'#02030a', bgl:4 }, defaultAlienXmasSettings(), load());
  apply(s0);
  // Initialize Doom runtime from initial state
  try{
    if (s0.dInt) ultra = (s0.dInt === 'ultra');
    if (typeof s0.dReduced === 'boolean') doomReduced = s0.dReduced;
    if (typeof s0.dVol === 'number') currentVolume = clamp(s0.dVol, 0, 1);
    if (CP.dInt) CP.dInt.value = s0.dInt || (ultra?'ultra':'normal');
    if (CP.dVol) CP.dVol.value = String(currentVolume);
    if (CP.dReduced) CP.dReduced.checked = !!doomReduced;
  }catch(e){}
  try{ activeTab = localStorage.getItem(TAB_STORE) || 'themes'; } catch{}
  applyTab(activeTab);
  function update(part){ const ns = Object.assign({}, state(), part); apply(ns); save(ns); }
  CP.theme && CP.theme.addEventListener('change', e => update({ theme: e.target.value }));
  CP.a1 && CP.a1.addEventListener('input', e => update({ a1: e.target.value }));
  CP.a2 && CP.a2.addEventListener('input', e => update({ a2: e.target.value }));
  CP.a3 && CP.a3.addEventListener('input', e => update({ a3: e.target.value }));
  CP.grid && CP.grid.addEventListener('input', e => update({ grid: parseInt(e.target.value,10) }));
  CP.scan && CP.scan.addEventListener('change', e => update({ scan: e.target.checked }));
  CP.laser && CP.laser.addEventListener('change', e => update({ laser: e.target.value }));
  CP.rainbow && CP.rainbow.addEventListener('input', e => update({ rainbow: parseFloat(e.target.value) }));
  CP.bgColor && CP.bgColor.addEventListener('input', e => update({ bg: e.target.value }));
  CP.bgBright && CP.bgBright.addEventListener('input', e => update({ bgl: parseInt(e.target.value,10) }));
  // Doom controls
  CP.dInt && CP.dInt.addEventListener('change', e => update({ dInt: e.target.value }));
  CP.dVol && CP.dVol.addEventListener('input', e => update({ dVol: parseFloat(e.target.value) }));
  CP.dReduced && CP.dReduced.addEventListener('change', e => update({ dReduced: e.target.checked }));
  CP.presetBlue && CP.presetBlue.addEventListener('click', () => update({ a1:'#00ffff', a2:'#00ff88', a3:'#ff00ff' }));
  CP.presetViolet && CP.presetViolet.addEventListener('click', () => update({ a1:'#9b8cff', a2:'#ff7de9', a3:'#ff00ff' }));
  CP.presetMiami && CP.presetMiami.addEventListener('click', () => update({ a1:'#00e5ff', a2:'#ff00a8', a3:'#ff8a00' }));
  CP.presetAlien && CP.presetAlien.addEventListener('click', () => update({ a1:'#39ff14', a2:'#0ff', a3:'#a1ff0a' }));
  CP.presetAlienXmas && CP.presetAlienXmas.addEventListener('click', () => update({ theme:'alien-xmas', a1:'#4ef3ff', a2:'#00ff88', a3:'#ff3366', bg:'#02020a', bgl:6, grid:40, scan:true }));
  CP.presetAmber && CP.presetAmber.addEventListener('click', () => update({ theme:'amber', a1:'#ffbf3b', a2:'#ffb347', a3:'#ff8c00' }));
  CP.presetSynth && CP.presetSynth.addEventListener('click', () => update({ theme:'synthwave', a1:'#00eaff', a2:'#2af598', a3:'#ff3cac' }));
  CP.presetRog && CP.presetRog.addEventListener('click', () => update({ theme:'rog', a1:'#ff1133', a2:'#00e5ff', a3:'#ff2255' }));
  CP.presetTealPurple && CP.presetTealPurple.addEventListener('click', () => update({ a1:'#00ffd1', a2:'#7a00ff', a3:'#cc66ff' }));
  CP.reset && CP.reset.addEventListener('click', () => { localStorage.removeItem(STORE); apply({ theme:'neon', a1:'#00ffff', a2:'#00ff88', a3:'#ff00ff', grid:40, scan:true }); save(state()); });
  for (const b of CP.tabs){ b.addEventListener('click', () => applyTab(b.dataset.tab)); }

  // Matrix canvas animation (Anime Matrix theme)
  const canvas = doc.getElementById('matrix-canvas');
  const ctx = canvas && canvas.getContext ? canvas.getContext('2d') : null;
  let cw=0,ch=0, dpr=1, cols=0, rows=0;
  function resize(){
    if (!canvas || !ctx) return;
    dpr = Math.max(1, Math.min(2, window.devicePixelRatio || 1));
    cw = canvas.clientWidth = window.innerWidth;
    ch = canvas.clientHeight = window.innerHeight;
    canvas.width = Math.floor(cw * dpr);
    canvas.height = Math.floor(ch * dpr);
    ctx.setTransform(dpr,0,0,dpr,0,0);
    const cell = 10; // pixel size
    cols = Math.ceil(cw / cell);
    rows = Math.ceil(ch / cell);
  }
  resize(); window.addEventListener('resize', resize);

  function drawMatrix(now){
    if (!canvas || !ctx || !body.classList.contains('theme-matrix')) return;
    const strong = body.classList.contains('lights-on');
    const cell = 10;
    ctx.clearRect(0,0,cw,ch);
    ctx.fillStyle = 'rgba(0,0,0,0.8)';
    ctx.fillRect(0,0,cw,ch);
    // draw dots
    for (let y=0; y<rows; y++){
      for (let x=0; x<cols; x++){
        // simple wave/random activation
        const v = (Math.sin((x+now/80)*0.5)+Math.cos((y+now/120)*0.7)) * 0.5 + Math.random()*0.3;
        if (v > 0.6){
          const a = strong ? 0.9 : 0.5;
          ctx.fillStyle = `rgba(0,255,136,${a})`;
          ctx.fillRect(x*cell+2, y*cell+2, 2, 2);
        }
      }
    }
  }

  // Laser canvas animation
  const lcanvas = doc.getElementById('laser-canvas');
  const lctx = lcanvas && lcanvas.getContext ? lcanvas.getContext('2d') : null;
  let lw=0, lh=0, ldpr=1;
  function resizeLaser(){
    if (!lcanvas || !lctx) return;
    ldpr = Math.max(1, Math.min(2, window.devicePixelRatio || 1));
    lw = lcanvas.clientWidth = window.innerWidth;
    lh = lcanvas.clientHeight = window.innerHeight;
    lcanvas.width = Math.floor(lw * ldpr);
    lcanvas.height = Math.floor(lh * ldpr);
    lctx.setTransform(ldpr,0,0,ldpr,0,0);
  }

  // Alien Xmas code-snow canvas
  const acanvas = doc.getElementById('alien-snow-canvas');
  const actx = acanvas && acanvas.getContext ? acanvas.getContext('2d') : null;
  let aw=0, ah=0, adpr=1;
  let flakes = [];
  const ALIEN_CHARS = '✶✷✸✹✺✻✦✧✩✪◇◆¤ᚠᚢᚦᚨᚱᚲᚷᚺᚾᛁᛃ';
  function resizeAlienSnow(){
    if (!acanvas || !actx) return;
    adpr = Math.max(1, Math.min(2, window.devicePixelRatio || 1));
    aw = acanvas.clientWidth = window.innerWidth;
    ah = acanvas.clientHeight = window.innerHeight;
    acanvas.width = Math.floor(aw * adpr);
    acanvas.height = Math.floor(ah * adpr);
    actx.setTransform(adpr,0,0,adpr,0,0);
    const count = Math.floor(Math.min(aw, ah) / 15); // Slightly fewer for calmness
    flakes = new Array(count).fill(0).map(()=>({
      x: Math.random()*aw,
      y: Math.random()*ah,
      v: 0.1 + Math.random()*0.3, // Slower fall
      sway: 15 + Math.random()*30, // Wider sway
      phase: Math.random()*Math.PI*2,
      type: Math.random() > 0.6 ? 'char' : 'orb', // Mix of chars and orbs
      ch: ALIEN_CHARS[Math.floor(Math.random()*ALIEN_CHARS.length)] || '*',
      size: 2 + Math.random()*4, // Smaller base size for orbs
      charSize: 10 + Math.random()*12,
      hue: 140 + Math.random()*180, // Cyan to Purple range
      blink: Math.random()*Math.PI*2
    }));
  }
  resizeAlienSnow(); window.addEventListener('resize', resizeAlienSnow);

  function drawAlienSnow(now){
    if (!acanvas || !actx || !body.classList.contains('theme-alien-xmas')) return;
    actx.clearRect(0,0,aw,ah);
    
    // Draw connections (Mathematical Correlations)
    actx.lineWidth = 0.5;
    for (let i=0; i<flakes.length; i++){
      const f1 = flakes[i];
      // Update physics
      f1.y += f1.v;
      f1.phase += 0.001;
      f1.blink += 0.02;
      const ox = Math.sin(now/2000 + f1.phase) * f1.sway;
      const x1 = f1.x + ox;
      const y1 = f1.y;

      if (f1.y > ah + 20){
        f1.y = -20;
        f1.x = Math.random()*aw;
      }

      // Draw particle
      const alpha = 0.2 + 0.5*(0.5+0.5*Math.sin(f1.blink));
      actx.fillStyle = `hsla(${f1.hue}, 100%, 75%, ${alpha})`;
      
      if (f1.type === 'char') {
        actx.font = `${f1.charSize}px Orbitron, monospace`;
        actx.textAlign = 'center';
        actx.textBaseline = 'middle';
        actx.fillText(f1.ch, x1, y1);
      } else {
        actx.beginPath();
        actx.arc(x1, y1, f1.size, 0, Math.PI*2);
        actx.fill();
        // Glow for orbs
        actx.shadowBlur = 10;
        actx.shadowColor = `hsla(${f1.hue}, 100%, 50%, 0.8)`;
        actx.fill();
        actx.shadowBlur = 0;
      }

      // Connect to neighbors
      for (let j=i+1; j<flakes.length; j++){
        const f2 = flakes[j];
        const ox2 = Math.sin(now/2000 + f2.phase) * f2.sway;
        const x2 = f2.x + ox2;
        const y2 = f2.y;
        
        const dx = x1 - x2;
        const dy = y1 - y2;
        const dist = Math.sqrt(dx*dx + dy*dy);

        if (dist < 100) { // Connection threshold
          const connAlpha = (1 - dist/100) * 0.15;
          actx.strokeStyle = `hsla(${f1.hue}, 100%, 80%, ${connAlpha})`;
          actx.beginPath();
          actx.moveTo(x1, y1);
          actx.lineTo(x2, y2);
          actx.stroke();
        }
      }
    }
  }
  resizeLaser(); window.addEventListener('resize', resizeLaser);

  function drawLaser(now){
    if (!lcanvas || !lctx || (!body.classList.contains('theme-laser'))) return;
    const strong = body.classList.contains('lights-on');
    const base = getVar('--neon-green') || '#00ff88';
    const accent = getVar('--neon-blue') || '#00ffff';
    lctx.clearRect(0,0,lw,lh);
    // Only additive strokes, no veil
    lctx.globalCompositeOperation = 'screen';
    lctx.lineWidth = strong ? 2.2 : 1.4;
    lctx.shadowBlur = strong ? 16 : 6;
    lctx.shadowColor = base;

    const cx = lw/2, cy = lh/2;
    const t = now/1000;
    const A = Math.min(lh, lw) * (strong ? 0.25 : 0.18);

    function plot(fn, color){
      lctx.beginPath();
      lctx.strokeStyle = color;
      const steps = Math.max(400, Math.floor(lw/3));
      for(let i=0;i<=steps;i++){
        const x = (i/steps)*lw;
        const y = fn(i/steps, x, t);
        if (i===0) lctx.moveTo(x,y); else lctx.lineTo(x,y);
      }
      lctx.stroke();
    }

    switch(laserMode){
      case 'sine':
        plot((u,x,tt)=> cy + Math.sin((u*8 + tt*2))*A, base);
        break;
      case 'square':
        plot((u,x,tt)=> cy + (Math.sin((u*8 + tt*3))>0?1:-1)*A*0.7, base);
        break;
      case 'triangle':
        plot((u,x,tt)=> cy + (2/Math.PI)*Math.asin(Math.sin((u*8 + tt*3)*Math.PI))*A*0.7, base);
        break;
      case 'saw':
        plot((u,x,tt)=> cy + (2*( (u*6 + tt*2) % 1) - 1)*A*0.7, base);
        break;
      case 'lissajous': {
        // Parametric figure
        lctx.beginPath();
        lctx.strokeStyle = accent;
        const n = 800;
        for(let i=0;i<=n;i++){
          const a = i/n * Math.PI*2;
          const x = cx + Math.sin(3*a + t*2)*A;
          const y = cy + Math.sin(4*a + t*2 + Math.PI/3)*A;
          if (i===0) lctx.moveTo(x,y); else lctx.lineTo(x,y);
        }
        lctx.stroke();
        break;
      }
      case 'qam': {
        const pts = [-3,-1,1,3];
        lctx.fillStyle = base;
        for (const px of pts) for (const py of pts){
          const x = cx + px * (A/2);
          const y = cy + py * (A/2);
          lctx.beginPath();
          lctx.arc(x + Math.sin(t*2+px)*2, y + Math.cos(t*1.5+py)*2, strong?3:2, 0, Math.PI*2);
          lctx.fill();
        }
        break;
      }
      case 'eye': {
        const traces = strong ? 40 : 20;
        for (let k=0;k<traces;k++){
          const phase = (k/traces)*Math.PI*2 + t*0.5;
          plot((u,x)=> cy + Math.tanh(Math.sin((u*8 + phase))*2)*A*0.6, base);
        }
        break;
      }
      case 'fft': {
        const bars = 64;
        const bw = lw / bars;
        for(let i=0;i<bars;i++){
          const v = (Math.sin(t*3 + i*0.35)+1)/2; // 0..1
          const h = v * lh * (strong?0.6:0.4);
          lctx.fillStyle = i%2?base:accent;
          lctx.fillRect(i*bw, lh-h, bw*0.8, h);
        }
        break;
      }
      case 'sweep':
      default: {
        const w = Math.max(2, lw*0.01);
        const x = ( (now/1200) % 1) * (lw + w*2) - w;
        const grad = lctx.createLinearGradient(x, 0, x+w, 0);
        grad.addColorStop(0, 'rgba(0,0,0,0)');
        grad.addColorStop(0.5, base);
        grad.addColorStop(1, 'rgba(0,0,0,0)');
        lctx.fillStyle = grad;
        lctx.fillRect(x, 0, w, lh);
        break;
      }
    }

    lctx.globalCompositeOperation = 'source-over';
  }

  // Doom canvas animation (fog, embers, drips, runes)
  const dcanvas = doc.getElementById('doom-canvas');
  const dctx = dcanvas && dcanvas.getContext ? dcanvas.getContext('2d') : null;
  let dw=0, dh=0, ddpr=1;
  let embers = [];
  let drips = [];
  let runes = [];
  let demons = [];
  let spits = [];
  let splatters = [];
  let shadows = [];
  let ultra = true;
  let doomReduced = false;
  let primeCd = 1800 + Math.floor(Math.random()*1200);
  // Lightning/thunder
  let thunderT = 0; // frames for active lightning arcs
  // Global doom ambiance
  let doomShakeT = 0; // frames of body/canvas shake
  let flashT = 0; // frames of lightning/hellflash
  let flashCd = 240 + Math.floor(Math.random()*600);
  const RUNES = 'ᚠᚢᚦᚨᚱᚲᚷᚺᚾᛁᛃᛇᛈᛉᛊᛏᛒᛖᛗᛚᛝᛟ';
  function resizeDoom(){
    if (!dcanvas || !dctx) return;
    ddpr = Math.max(1, Math.min(2, window.devicePixelRatio || 1));
    dw = dcanvas.clientWidth = window.innerWidth;
    dh = dcanvas.clientHeight = window.innerHeight;
    dcanvas.width = Math.floor(dw * ddpr);
    dcanvas.height = Math.floor(dh * ddpr);
    dctx.setTransform(ddpr,0,0,ddpr,0,0);
    // reinit particles to fit screen
    initDoomElements();
  }
  function rand(min, max){ return Math.random()*(max-min)+min; }
  function clamp(v, lo, hi){ return Math.max(lo, Math.min(hi, v)); }
  function initDoomElements(){
    // Embers
    const count = ultra ? Math.max(90, Math.floor(Math.min(dw, dh)/12)) : Math.max(60, Math.floor(Math.min(dw, dh)/16));
    embers = new Array(count).fill(0).map(()=>({
      x: Math.random()*dw,
      y: dh + Math.random()*dh*0.5,
      v: rand(0.2, 0.6),
      r: rand(0.8, 2.2),
      a: rand(0.2, 0.6),
      o: Math.random()*Math.PI*2,
    }));
    // Drips
    const dcount = ultra ? 18 : 12;
    drips = new Array(dcount).fill(0).map(()=>({
      x: Math.random()*dw,
      y: rand(-80, -10),
      v: rand(0.6, 1.6),
      w: rand(2, 5),
      len: rand(30, 120),
      sway: rand(8, 24),
      phase: Math.random()*Math.PI*2,
    }));
    // Shadows (large dark drifting blobs)
    const sh = ultra ? 4 : 2;
    shadows = new Array(sh).fill(0).map(()=>({
      x: Math.random()*dw,
      y: Math.random()*dh,
      r: rand(Math.max(dw,dh)*0.3, Math.max(dw,dh)*0.6),
      vx: rand(-0.06, 0.06),
      vy: rand(-0.04, 0.04),
      a: rand(0.05, 0.12)
    }));
    // Runes (grid of faint glyphs)
    runes = [];
    const cell = 90;
    const cols = Math.ceil(dw / cell);
    const rows = Math.ceil(dh / cell);
    for (let y=0; y<rows; y++){
      for (let x=0; x<cols; x++){
        runes.push({
          x: x*cell + rand(-8,8),
          y: y*cell + rand(-8,8),
          ch: RUNES[Math.floor(Math.random()*RUNES.length)] || 'ᛟ',
          a: rand(0.08, 0.18),
          s: rand(16, 26)
        });
      }
    }
    // Flying abyssal orbs (ominous, non-infringing)
  const demonCount = ultra ? clamp(Math.floor(Math.min(dw, dh)/120), 12, 34) : clamp(Math.floor(Math.min(dw, dh)/160), 8, 24);
  demons = new Array(demonCount).fill(0).map(()=>{
      const spikes = Math.floor(rand(16, 28));
      const spikesVar = new Array(spikes).fill(0).map(()=> rand(0.6, 1.45));
      const cracks = new Array(Math.floor(rand(2,4))).fill(0).map(()=>({
        a: rand(0, Math.PI*2),
        l: rand(0.35, 0.9)
      }));
      // Variant selection
      const vr = Math.random();
      const variant = (vr < (ultra?0.35:0.25)) ? 'warden' : (vr < (ultra?0.65:0.5) ? 'watcher' : 'stalker');
      return {
        x: Math.random()*dw,
        y: Math.random()*dh,
        vx: rand(-0.2, 0.2),
        vy: rand(-0.12, 0.12),
        size: variant==='warden' ? rand(64, 100) : (variant==='stalker' ? rand(28, 56) : rand(40, 78)),
        spin: rand(-0.03, 0.03),
        angle: Math.random()*Math.PI*2,
        spikes,
        spikesVar,
        bobPhase: Math.random()*Math.PI*2,
        bobSpeed: rand(0.002, 0.006),
        eyePhase: Math.random()*Math.PI*2,
        eyeSpeed: rand(0.005, 0.011),
        hue: variant==='watcher' ? rand(330, 350) : rand(0, 16), // watcher: colder crimson
        jitterT: 0,
        jitterEvery: Math.floor(rand(28, 90)),
        cracks,
        // steering target for stalking glide
        tx: 0, ty: 0, tLife: 0,
  maxSpeed: (variant==='stalker' ? rand(1.2, 2.0) : (ultra ? rand(1.0, 1.6) : rand(0.7, 1.3))),
  accel: (variant==='stalker' ? rand(0.006, 0.012) : (ultra ? rand(0.004, 0.009) : rand(0.003, 0.007))),
        // eyelid params for diabolic squint (eyes)
        lidBase: rand(0.28, 0.5),
        lidAmp: rand(0.08, 0.18),
        lidPhase: Math.random()*Math.PI*2,
        lidSpeed: rand(0.004, 0.010),
        // mouth/jaw animation
        mouthPhase: Math.random()*Math.PI*2,
        mouthSpeed: variant==='warden' ? rand(0.006, 0.014) : rand(0.008, 0.016),
        mouthBase: variant==='stalker' ? rand(0.10, 0.20) : rand(0.12, 0.25),
        mouthAmp: variant==='warden' ? rand(0.24, 0.42) : rand(0.18, 0.35),
        // lunge behavior
        lungeT: 0,
        lungeCd: Math.floor(rand(160, 520)),
        // crown eyes (small eyes ring)
        eyelets: (function(){
          const n = (variant==='watcher' ? Math.floor(rand(10, 16)) : Math.floor(rand(6, 10)));
          const arr = [];
          for(let i=0;i<n;i++){
            arr.push({
              ang: (i/n)*Math.PI*1.4 + rand(-0.2, 0.2) - Math.PI*0.7,
              r: rand(0.5, 0.95),
              blinkPhase: Math.random()*Math.PI*2,
              blinkSpeed: rand(0.02, 0.05)
            });
          }
          return arr;
        })(),
        beamT: 0,
        beamCd: variant==='watcher' ? Math.floor(rand(60, 220)) : Math.floor(rand(120, 500)),
        variant
      };
    });
    // initialize stalking targets
    for (const d of demons){
      d.tx = d.x + rand(-dw*0.25, dw*0.25);
      d.ty = d.y + rand(-dh*0.25, dh*0.25);
      d.tLife = Math.floor(rand(140, 280));
    }
  }
  resizeDoom(); window.addEventListener('resize', resizeDoom);

  function drawFog(now){
    // Layered drifting radial fog
    const layers = 3;
    for (let i=0;i<layers;i++){
      const t = now/10000 + i*10;
      const cx = (Math.sin(t*0.8 + i)*0.5+0.5) * (dw+400) - 200;
      const cy = (Math.cos(t*0.6 + i*1.3)*0.5+0.5) * (dh+400) - 200;
      const r = Math.max(dw, dh) * (0.6 + i*0.25);
      const g = dctx.createRadialGradient(cx, cy, 0, cx, cy, r);
      g.addColorStop(0, 'rgba(180,0,0,0.06)');
      g.addColorStop(1, 'rgba(0,0,0,0)');
      dctx.fillStyle = g;
      dctx.beginPath(); dctx.arc(cx, cy, r, 0, Math.PI*2); dctx.fill();
    }
  }
  function drawEmbers(now){
    dctx.globalCompositeOperation = 'screen';
    for (const p of embers){
      p.y -= p.v * (1 + 0.3*Math.sin(now/500 + p.o));
      p.x += 0.2*Math.sin(now/900 + p.o);
      if (p.y < -20){ p.y = dh + rand(10, 80); p.x = Math.random()*dw; }
      dctx.beginPath();
      dctx.fillStyle = `rgba(255, ${Math.floor(60+120*Math.random())}, 0, ${p.a})`;
      dctx.arc(p.x, p.y, p.r, 0, Math.PI*2);
      dctx.fill();
    }
    dctx.globalCompositeOperation = 'source-over';
  }
  function drawSpits(now){
    // Glowing projectiles with slight trail; remove when offscreen or faded
    const next = [];
    dctx.globalCompositeOperation = 'screen';
    for (const s of spits){
      s.x += s.vx; s.y += s.vy;
      s.age++;
      s.alpha *= 0.992; // slow fade
      // trail
      dctx.strokeStyle = `rgba(255, ${Math.floor(120+80*Math.sin(s.seed))}, 40, ${Math.max(0, s.alpha*0.6)})`;
      dctx.lineWidth = 2.2;
      dctx.beginPath(); dctx.moveTo(s.x - s.vx*3, s.y - s.vy*3); dctx.lineTo(s.x, s.y); dctx.stroke();
      // head glow
      const rg = dctx.createRadialGradient(s.x, s.y, 0, s.x, s.y, s.r*3);
      rg.addColorStop(0, `rgba(255, 150, 60, ${s.alpha})`);
      rg.addColorStop(1, 'rgba(0,0,0,0)');
      dctx.fillStyle = rg; dctx.beginPath(); dctx.arc(s.x, s.y, s.r*3, 0, Math.PI*2); dctx.fill();
      // core
      dctx.fillStyle = `rgba(255, 220, 180, ${Math.max(0, s.alpha)})`;
      dctx.beginPath(); dctx.arc(s.x, s.y, s.r, 0, Math.PI*2); dctx.fill();
      if (s.x<-40 || s.x>dw+40 || s.y<-40 || s.y>dh+40 || s.alpha<0.05 || s.age>1200){
        // If exiting screen, create blood splatter at edge
        if (s.x<-40 || s.x>dw+40 || s.y<-40 || s.y>dh+40){
          const ex = clamp(s.x, 5, dw-5);
          const ey = clamp(s.y, 5, dh-5);
          const drops = [];
          const n = ultra ? 18 : 10;
          for (let i=0;i<n;i++){
            drops.push({
              x: rand(-10,10), y: rand(-10,10), rx: rand(2,6), ry: rand(1,4), rz: rand(0, Math.PI)
            });
          }
          splatters.push({ x: ex, y: ey, rot: Math.random()*Math.PI, drops, alpha: 0.6, age: 0 });
          playSplatFX();
        } else if (Math.random()<0.5){
          dctx.fillStyle = 'rgba(255,120,40,0.5)';
          for(let i=0;i<4;i++){ dctx.fillRect(s.x+rand(-2,2), s.y+rand(-2,2), 2,2); }
        }
        continue;
      }
      next.push(s);
    }
    spits = next;
    dctx.globalCompositeOperation = 'source-over';
  }
  function drawDrips(now){
    dctx.strokeStyle = 'rgba(200,0,0,0.4)';
    dctx.lineCap = 'round';
    for (const d of drips){
      const sway = Math.sin(now/800 + d.phase) * d.sway;
      const x0 = d.x + sway*0.2, y0 = d.y;
      const x1 = d.x + sway*0.8, y1 = d.y + d.len*0.5;
      const x2 = d.x + sway, y2 = d.y + d.len;
      dctx.lineWidth = d.w;
      dctx.beginPath();
      dctx.moveTo(x0, y0);
      dctx.quadraticCurveTo(x1, y1, x2, y2);
      dctx.stroke();
      d.y += d.v;
      if (d.y > dh + 40){ d.y = rand(-120, -20); d.x = Math.random()*dw; }
    }
  }
  function drawShadows(now){
    dctx.globalCompositeOperation = 'multiply';
    for (const s of shadows){
      s.x += s.vx; s.y += s.vy;
      if (s.x < -s.r) s.x = dw + s.r; else if (s.x > dw + s.r) s.x = -s.r;
      if (s.y < -s.r) s.y = dh + s.r; else if (s.y > dh + s.r) s.y = -s.r;
      const g = dctx.createRadialGradient(s.x, s.y, 0, s.x, s.y, s.r);
      g.addColorStop(0, `rgba(0,0,0,${s.a})`);
      g.addColorStop(1, 'rgba(0,0,0,0)');
      dctx.fillStyle = g;
      dctx.beginPath(); dctx.arc(s.x, s.y, s.r, 0, Math.PI*2); dctx.fill();
    }
    dctx.globalCompositeOperation = 'source-over';
  }
  function drawSplatters(now){
    // Persistent blood at edges; slow fade
    const keep = [];
    for (const sp of splatters){
      sp.alpha *= 0.996;
      sp.age++;
      if (sp.alpha < 0.04 || sp.age>4000) continue;
      dctx.save();
      dctx.translate(sp.x, sp.y);
      dctx.rotate(sp.rot);
      dctx.fillStyle = `rgba(150,0,0,${sp.alpha})`;
      for (const d of sp.drops){
        dctx.beginPath(); dctx.ellipse(d.x, d.y, d.rx, d.ry, d.rz, 0, Math.PI*2); dctx.fill();
      }
      dctx.restore();
      keep.push(sp);
    }
    splatters = keep;
  }
  function drawRunes(now){
    const strong = body.classList.contains('lights-on');
    dctx.font = '600 20px Orbitron, sans-serif';
    dctx.textAlign = 'center'; dctx.textBaseline = 'middle';
    for (const r of runes){
      const pul = r.a + 0.06*Math.sin((r.x+r.y+now)/1400);
      const flashBoost = flashT>0 ? 1.8 : 1.0;
      dctx.fillStyle = `rgba(255, 60, 0, ${(strong?pul*1.2:pul)*flashBoost})`;
      dctx.save();
      dctx.translate(r.x, r.y);
      dctx.rotate( (Math.sin((r.x*13+r.y*7+now)/5000))*0.1 );
      dctx.scale(r.s/20, r.s/20);
      dctx.fillText(r.ch, 0, 0);
      dctx.restore();
    }
  }
  function drawHellflash(){
    if (flashT > 0){
      flashT--;
      dctx.globalCompositeOperation = 'screen';
      const a = 0.08 + 0.06*Math.random();
      const g = dctx.createRadialGradient(dw*0.5, dh*0.45, 0, dw*0.5, dh*0.45, Math.max(dw, dh));
      g.addColorStop(0, `rgba(255, 200, 160, ${a})`);
      g.addColorStop(1, 'rgba(200,0,0,0)');
      dctx.fillStyle = g;
      dctx.fillRect(0,0,dw,dh);
      // Lightning arcs when thunder active
      if (thunderT > 0){
        thunderT--;
        drawLightning();
      }
      dctx.globalCompositeOperation = 'source-over';
    } else if (--flashCd <= 0){
      // reset cooldown randomly
      flashCd = 240 + Math.floor(Math.random()*600);
      // Occasionally trigger thunder event
      if (Math.random() < (ultra?0.35:0.18)) triggerThunder();
    }
  }
  function triggerThunder(){
    const sf = doomReduced ? 0.6 : 1.0;
    flashT = Math.floor(rand(10, 20)*sf);
    thunderT = Math.floor(rand(6, 12)*sf);
    doomShakeT = Math.max(doomShakeT, Math.floor((ultra ? 28 : 16)*sf));
    playThunderFX();
    // rumble spike
    try{ if (masterGain && rumbleGain && audioCtx){ masterGain.gain.setTargetAtTime(Math.max(masterGain.gain.value, 0.75), audioCtx.currentTime, 0.05); setTimeout(()=>{ try{ masterGain.gain.setTargetAtTime(currentVolume, audioCtx.currentTime, 0.2);}catch(e){} }, 180); } }catch(e){}
  }
  function drawLightning(){
    dctx.save();
    dctx.globalCompositeOperation = 'screen';
    dctx.strokeStyle = 'rgba(255,220,200,0.7)';
    dctx.lineWidth = 2;
    const strikes = ultra ? 3 : 2;
    for (let i=0;i<strikes;i++){
      const x0 = rand(0, dw), y0 = rand(0, dh*0.4);
      const x1 = x0 + rand(-dw*0.2, dw*0.2), y1 = dh - rand(0, dh*0.2);
      drawJag(x0,y0,x1,y1, 7);
    }
    dctx.restore();
    function drawJag(x0,y0,x1,y1, seg){
      let prev = {x:x0,y:y0};
      for (let k=1;k<=seg;k++){
        const u = k/seg;
        const x = x0 + (x1-x0)*u + rand(-18,18)*(1-u);
        const y = y0 + (y1-y0)*u + rand(-10,10)*(1-u);
        dctx.beginPath(); dctx.moveTo(prev.x, prev.y); dctx.lineTo(x,y); dctx.stroke();
        prev = {x,y};
      }
    }
  }
  function drawDemons(now){
    dctx.globalCompositeOperation = 'source-over';
    for (const d of demons){
      // Targeting and predatory lunges
      d.tLife--;
      const dx = d.tx - d.x, dy = d.ty - d.y;
      const dist = Math.hypot(dx, dy) || 1;
      if (d.tLife <= 0 || dist < d.size*1.6){
        d.tx = d.x + rand(-dw*0.35, dw*0.35);
        d.ty = d.y + rand(-dh*0.35, dh*0.35);
        d.tLife = Math.floor(rand(120, 260));
      }
      // Lunge trigger
      const lungeChance = ultra ? 0.008 : 0.003;
      if (d.lungeT > 0) d.lungeT--; else if (d.lungeCd > 0) d.lungeCd--; else if (Math.random() < lungeChance){
        d.lungeT = Math.floor(rand(40, 100));
        d.lungeCd = Math.floor(rand(260, 640));
        // push target forward to create a pounce direction
        const ang = Math.atan2(d.vy||Math.sin(now/1000), d.vx||Math.cos(now/1000));
        d.tx = d.x + Math.cos(ang) * rand(220, 420);
        d.ty = d.y + Math.sin(ang) * rand(180, 320);
  // trigger global shake and occasional flash
  const sf = doomReduced ? 0.6 : 1.0;
  doomShakeT = Math.max(doomShakeT, Math.floor((ultra ? 24 : 14)*sf));
  if (Math.random() < (ultra?0.35:0.15)*sf) { flashT = Math.floor(rand(6, 14)*sf); }
        // audio: lunge FX
        playLungeFX();
        // chance to spit on lunge
  const spitChance = ultra ? 0.85 : 0.6;
  if (Math.random() < spitChance*(doomReduced?0.6:1.0)){
          const spd = rand(2.6, 4.6);
          spits.push({
            x: d.x + Math.cos(ang)*d.size*0.4,
            y: d.y + Math.sin(ang)*d.size*0.2,
            vx: Math.cos(ang)*spd + rand(-0.3,0.3),
            vy: Math.sin(ang)*spd + rand(-0.2,0.2),
            r: rand(2, 3.2),
            alpha: 0.95,
            age: 0,
            seed: Math.random()*Math.PI*2
          });
          if (d.variant==='prime'){
            const spread = 0.25;
            for (const off of [-spread, spread]){
              const aa = ang + off;
              const spd2 = spd * rand(0.9, 1.1);
              spits.push({ x: d.x + Math.cos(aa)*d.size*0.4, y: d.y + Math.sin(aa)*d.size*0.2, vx: Math.cos(aa)*spd2 + rand(-0.25,0.25), vy: Math.sin(aa)*spd2 + rand(-0.2,0.2), r: rand(2,3.4), alpha: 0.95, age: 0, seed: Math.random()*Math.PI*2 });
            }
          }
          playSpitFX();
        }
      }
      const effMax = d.maxSpeed * (d.lungeT>0 ? 1.85 : 1.0);
      const desVx = (dx/dist) * effMax;
      const desVy = (dy/dist) * effMax;
      d.vx += (desVx - d.vx) * d.accel;
      d.vy += (desVy - d.vy) * d.accel;
      // Small jitter bursts
      d.jitterT++;
      if (d.jitterT % d.jitterEvery === 0){
        d.vx = clamp(d.vx + rand(-0.08, 0.08), -effMax*1.1, effMax*1.1);
        d.vy = clamp(d.vy + rand(-0.06, 0.06), -effMax*1.1, effMax*1.1);
        d.jitterEvery = Math.floor(rand(36, 96));
      }
      // Clamp speed
      const sp = Math.hypot(d.vx, d.vy) || 1e-6;
      if (sp > effMax){ d.vx *= effMax/sp; d.vy *= effMax/sp; }

      d.x += d.vx; d.y += d.vy;
      d.angle = Math.atan2(d.vy, d.vx);
      d.bobPhase += d.bobSpeed * (d.lungeT>0 ? 0.3 : 1);
      d.eyePhase += d.eyeSpeed * (d.lungeT>0 ? 1.4 : 1);
      d.lidPhase += d.lidSpeed;
      d.mouthPhase += d.mouthSpeed * (d.lungeT>0 ? 1.3 : 1);
      // Wrap edges
      if (d.x < -d.size*2) d.x = dw + d.size;
      if (d.x > dw + d.size*2) d.x = -d.size;
      if (d.y < -d.size*2) d.y = dh + d.size;
      if (d.y > dh + d.size*2) d.y = -d.size;

  // Prime boss scaling
  const sizeMul = (d.variant==='prime') ? 1.6 : 1.0;
  const R = d.size*0.6*sizeMul;
      const bob = Math.sin(d.bobPhase) * (d.size*0.04);
  const mouthOpen = clamp(d.mouthBase + Math.sin(d.mouthPhase)*d.mouthAmp + (d.lungeT>0?(d.variant==='prime'?0.5:0.35):0), 0.08, 0.95);

      dctx.save();
  dctx.translate(d.x, d.y + bob);

      // Elongated shadow behind
  dctx.save();
  dctx.rotate(d.angle + Math.PI);
      dctx.fillStyle = 'rgba(0,0,0,0.45)';
      dctx.beginPath(); dctx.ellipse(R*0.7, 0, R*0.65, R*0.2, 0, 0, Math.PI*2); dctx.fill();
      dctx.restore();

  // Abyss Warden head silhouette (tri-lobed, scarred)
      dctx.beginPath();
      const steps = 44;
      for(let i=0;i<=steps;i++){
        const a = (i/steps)*Math.PI*2;
        // tri-lobed skull form
        const lobes = 0.18*Math.sin(3*a + d.bobPhase*0.4);
        const scars = 0.07*Math.cos(5*a + d.eyePhase*0.3);
        const noise = 1.0 + lobes + scars;
        const rad = R * 1.06 * noise;
        const x = Math.cos(a) * rad;
        const y = Math.sin(a) * rad * (1 - 0.05*Math.cos(a*2));
        if (i===0) dctx.moveTo(x,y); else dctx.lineTo(x,y);
      }
  dctx.closePath();
  const hg = dctx.createRadialGradient(-R*0.12, -R*0.18, R*0.25, 0, 0, R*1.2);
      hg.addColorStop(0, `hsla(${d.hue+4}, 70%, 32%, 1)`);
      hg.addColorStop(0.6, `hsla(${d.hue-2}, 65%, 20%, 1)`);
      hg.addColorStop(1, `hsla(${d.hue-12}, 60%, 10%, 1)`);
  dctx.fillStyle = hg; dctx.fill();
  // silhouette rim
  dctx.strokeStyle = 'rgba(0,0,0,0.7)';
  dctx.lineWidth = Math.max(1.5, R*0.04);
  dctx.stroke();

      // Mandible tusks (bigger for warden)
      dctx.fillStyle = 'rgba(240,230,220,0.95)';
      const tuskScale = d.variant==='warden' ? 1.3 : 1.0;
      for (const sgn of [-1,1]){
        dctx.beginPath();
        dctx.moveTo(R*0.25, sgn*R*0.35);
        dctx.quadraticCurveTo(R*0.5, sgn*R*0.5, R*0.52, sgn*R*0.15*tuskScale);
        dctx.lineTo(R*0.42, sgn*R*0.1);
        dctx.closePath(); dctx.fill();
      }
      if (d.variant==='warden'){
        // extra side tusks
        for (const sgn of [-1,1]){
          dctx.beginPath();
          dctx.moveTo(R*0.12, sgn*R*0.28);
          dctx.quadraticCurveTo(R*0.3, sgn*R*0.4, R*0.34, sgn*R*0.1);
          dctx.lineTo(R*0.26, sgn*R*0.06);
          dctx.closePath(); dctx.fill();
        }
      }

  // Crown nubs (bluish spikes)
      dctx.fillStyle = `hsla(${(d.hue+210)%360}, 45%, 55%, 0.95)`;
      const hornL = R*0.45, hornB = R*0.4;
      for (const sgn of [-1, 1]){
        dctx.beginPath();
        dctx.moveTo(-R*0.18, -sgn*hornB*0.5);
        dctx.quadraticCurveTo(-R*0.02, -sgn*hornB*1.2, R*0.1, -sgn*hornB*1.25);
        dctx.lineTo(R*0.2, -sgn*hornB*1.05);
        dctx.lineTo(-R*0.08, -sgn*hornB*0.2);
        dctx.closePath(); dctx.fill();
      }

  // Single central eye (glowing)
  const eR = R*(d.variant==='stalker'?0.26:0.30);
      dctx.save(); dctx.translate(-R*0.04, -R*0.1);
      const eglow = dctx.createRadialGradient(0,0, eR*0.2, 0,0, eR*1.3);
      eglow.addColorStop(0, 'rgba(255,90,20,0.95)');
      eglow.addColorStop(1, 'rgba(60,0,0,0)');
      dctx.fillStyle = eglow; dctx.beginPath(); dctx.arc(0,0, eR*1.2, 0, Math.PI*2); dctx.fill();
      // sclera
      dctx.fillStyle = 'rgba(240,230,220,0.98)';
      dctx.beginPath(); dctx.arc(0,0, eR, 0, Math.PI*2); dctx.fill();
      // iris
      const irisR = eR*0.6;
      const ig = dctx.createRadialGradient(0,0, irisR*0.2, 0,0, irisR);
      ig.addColorStop(0, `hsla(${d.hue+30}, 90%, 46%, 1)`);
      ig.addColorStop(1, `hsla(${d.hue+10}, 90%, 26%, 1)`);
      dctx.fillStyle = ig; dctx.beginPath(); dctx.arc(0,0, irisR, 0, Math.PI*2); dctx.fill();
      // pupil (round, menacing)
      dctx.fillStyle = 'rgba(5,5,7,1)';
      dctx.beginPath(); dctx.arc(0,0, irisR*0.5, 0, Math.PI*2); dctx.fill();
      // lids
      const lidOpen = clamp(d.lidBase*0.9 + Math.sin(d.lidPhase)*d.lidAmp*0.8, 0.15, 0.8);
      dctx.fillStyle = `rgba(28, 5, 5, 0.98)`;
      dctx.beginPath(); dctx.moveTo(-eR,0); dctx.quadraticCurveTo(0, -eR*(0.5+0.6*lidOpen), eR, 0); dctx.lineTo(eR, -eR*1.3); dctx.lineTo(-eR, -eR*1.3); dctx.closePath(); dctx.fill();
      dctx.beginPath(); dctx.moveTo(-eR,0); dctx.quadraticCurveTo(0, eR*(0.35+0.45*lidOpen), eR, 0); dctx.lineTo(eR, eR*1.3); dctx.lineTo(-eR, eR*1.3); dctx.closePath(); dctx.fill();
      dctx.restore();

      // Crown of small eyes (blink and occasional rays)
      for (const e of d.eyelets){
        e.blinkPhase += e.blinkSpeed;
        const open = clamp(0.2 + 0.8*(0.5+0.5*Math.sin(e.blinkPhase)), 0.05, 1);
        const ca = Math.cos(e.ang), sa = Math.sin(e.ang);
        const ex = ca * R * e.r;
        const ey = sa * R * e.r - R*0.3; // crown arc above
        const r = R*0.07 * open;
        // glow
        const g = dctx.createRadialGradient(ex, ey, r*0.2, ex, ey, r*2.2);
        g.addColorStop(0, 'rgba(255,80,20,0.8)');
        g.addColorStop(1, 'rgba(60,0,0,0)');
        dctx.fillStyle = g; dctx.beginPath(); dctx.arc(ex, ey, r*1.6, 0, Math.PI*2); dctx.fill();
        // eyeball
        dctx.fillStyle = 'rgba(242,232,220,0.95)';
        dctx.beginPath(); dctx.ellipse(ex, ey, r*1.1, r*0.9, 0, 0, Math.PI*2); dctx.fill();
        // tiny pupil
        dctx.fillStyle = 'rgba(10,10,12,1)';
        dctx.beginPath(); dctx.arc(ex, ey, r*0.45, 0, Math.PI*2); dctx.fill();
      }
      // occasional rays
      if (d.beamT > 0) d.beamT--; else if (d.beamCd > 0) d.beamCd--; else if (Math.random() < 0.01){
        d.beamT = Math.floor(rand(6, 18));
        d.beamCd = Math.floor(rand(200, 700));
      }
      if (d.beamT > 0){
        dctx.save();
        dctx.globalCompositeOperation = 'screen';
        dctx.strokeStyle = 'rgba(255,120,60,0.35)';
        dctx.lineWidth = 1;
        const ei = Math.floor(Math.random()*d.eyelets.length);
        const e = d.eyelets[ei];
        const ca = Math.cos(e.ang), sa = Math.sin(e.ang);
        const ex = ca * R * e.r;
        const ey = sa * R * e.r - R*0.3;
        const len = R*rand(0.8, 1.6);
        dctx.beginPath();
        dctx.moveTo(ex, ey);
        dctx.lineTo(ex + ca*len, ey + sa*len);
        dctx.stroke();
        dctx.restore();
      }

    // Horizontal maw
    const mW = R*(d.variant==='stalker'?0.95:1.1), mH = R*(0.18 + 0.6*mouthOpen*(d.variant==='warden'||d.variant==='prime'?1.2:1));
      dctx.save(); dctx.translate(0, R*0.25);
      // Inner glow gradient
      const mg = dctx.createRadialGradient(0,0, mH*0.2, 0,0, mH*1.2);
      mg.addColorStop(0, 'rgba(255,120,40,0.9)');
      mg.addColorStop(0.6, 'rgba(130,20,0,0.9)');
      mg.addColorStop(1, 'rgba(0,0,0,1)');
      // Mouth cavity
      dctx.fillStyle = mg;
      dctx.beginPath(); dctx.ellipse(0,0, mW*0.5, mH, 0, 0, Math.PI*2); dctx.fill();
      // Teeth: upper and lower rows
      dctx.fillStyle = 'rgba(245,235,220,0.98)';
  const tN = d.variant==='stalker'?22:(d.variant==='warden'?32:28);
      for(let i=0;i<tN;i++){
        const u = i/(tN-1);
        const ax = (u-0.5) * mW*0.92;
        const bias = (1-Math.abs(u-0.5)*2);
        const lenU = R*0.26 * (0.5 + 1.0*bias) * (i%2?1:0.8);
        const lenL = R*0.26 * (0.5 + 1.0*bias) * (i%2?0.9:1);
        // upper fang
        dctx.beginPath();
        dctx.moveTo(ax-2, -mH*0.2);
        dctx.lineTo(ax, -mH*0.2 - lenU);
        dctx.lineTo(ax+2, -mH*0.2);
        dctx.closePath(); dctx.fill();
        // lower fang
        dctx.beginPath();
        dctx.moveTo(ax-2, mH*0.2);
        dctx.lineTo(ax, mH*0.2 + lenL);
        dctx.lineTo(ax+2, mH*0.2);
        dctx.closePath(); dctx.fill();
      }
      // Gore/drool threads
      dctx.strokeStyle = 'rgba(160,20,10,0.6)';
      dctx.lineWidth = 1.5;
      const threads = 3;
      for(let k=0;k<threads;k++){
        const ax = (Math.random()*2-1) * (mW*0.45);
        const len = mH*rand(0.6, 1.2);
        const sway = Math.sin((now/700)+k*1.7 + d.x*0.01) * len*0.15;
        dctx.beginPath();
        dctx.moveTo(ax, -mH*0.02);
        dctx.quadraticCurveTo(ax+sway*0.5, mH*0.18, ax+sway, mH*0.02 + len);
        dctx.stroke();
      }
      dctx.restore();

      // Scar veins overlay
      dctx.save();
      dctx.globalAlpha = 0.35;
      dctx.strokeStyle = `rgba(80,0,0,0.7)`;
      dctx.lineWidth = Math.max(0.8, R*0.015);
      for (const c of d.cracks){
        const a0 = c.a, len = c.l*R;
        const x0 = Math.cos(a0)*R*0.2, y0 = Math.sin(a0)*R*0.2;
        const x1 = Math.cos(a0)*len*0.9, y1 = Math.sin(a0)*len*0.9;
        dctx.beginPath(); dctx.moveTo(x0,y0);
        // slight wiggle
        const midx = (x0+x1)/2 + rand(-R*0.05, R*0.05);
        const midy = (y0+y1)/2 + rand(-R*0.05, R*0.05);
        dctx.quadraticCurveTo(midx, midy, x1, y1);
        dctx.stroke();
      }
      dctx.restore();

      // Perimeter spikes (small nubs)
      dctx.fillStyle = `hsla(${d.hue-8}, 55%, 18%, 0.95)`;
      const nSp = 18;
      for(let i=0;i<nSp;i++){
        const a = (i/nSp)*Math.PI*2 + 0.1*Math.sin(d.bobPhase+i);
        const ca = Math.cos(a), sa = Math.sin(a);
        const x0 = ca*(R*1.05), y0 = sa*(R*1.05);
        const x1 = ca*(R*1.28), y1 = sa*(R*1.28);
        const xL = x0 - sa*3, yL = y0 + ca*3;
        const xR = x0 + sa*3, yR = y0 - ca*3;
        dctx.beginPath(); dctx.moveTo(xL,yL); dctx.lineTo(x1,y1); dctx.lineTo(xR,yR); dctx.closePath(); dctx.fill();
      }

      // Flesh blotches for texture
      dctx.globalAlpha = 0.12;
      for(let i=0;i<4;i++){
        const bx = rand(-R*0.6, R*0.6), by = rand(-R*0.6, R*0.6);
        const br = rand(R*0.1, R*0.22);
        const bg = dctx.createRadialGradient(bx, by, 0, bx, by, br);
        bg.addColorStop(0, `hsla(${d.hue-8}, 70%, 24%, 1)`);
        bg.addColorStop(1, 'rgba(0,0,0,0)');
        dctx.fillStyle = bg;
        dctx.beginPath(); dctx.arc(bx, by, br, 0, Math.PI*2); dctx.fill();
      }
      dctx.globalAlpha = 1;

      dctx.restore();
    }
  }
  function drawDoom(now){
    if (!dcanvas || !dctx || !body.classList.contains('theme-doom')) return;
    // Occasional boss spawn timer
    if (--primeCd <= 0 && demons.every(x=>x.variant!=='prime')){ spawnPrime(); primeCd = 2000 + Math.floor(Math.random()*2600); }
    dctx.clearRect(0,0,dw,dh);
    // screen shake jitter (canvas-only) and body microshake
    if (doomShakeT > 0){
      doomShakeT--;
      const sx = (Math.random()*2-1) * (ultra?7:3);
      const sy = (Math.random()*2-1) * (ultra?7:3);
      dctx.save(); dctx.translate(sx, sy);
      body.classList.add('doom-shake');
      body.style.setProperty('--shake-x', sx.toFixed(1)+'px');
      body.style.setProperty('--shake-y', sy.toFixed(1)+'px');
    } else {
      body.classList.remove('doom-shake');
      body.style.removeProperty('--shake-x');
      body.style.removeProperty('--shake-y');
    }
    // subtle dark veil
    dctx.fillStyle = 'rgba(0,0,0,0.55)';
    dctx.fillRect(0,0,dw,dh);
    drawShadows(now);
    drawFog(now);
    drawEmbers(now);
    drawRunes(now);
    drawDrips(now);
    drawDemons(now);
    drawSpits(now);
    drawSplatters(now);
    // Red vignette overlay
    const vg = dctx.createRadialGradient(dw*0.5, dh*0.55, Math.min(dw, dh)*0.2, dw*0.5, dh*0.55, Math.max(dw, dh)*0.7);
    vg.addColorStop(0, 'rgba(0,0,0,0)');
    vg.addColorStop(1, 'rgba(60,0,0,0.75)');
    dctx.fillStyle = vg; dctx.fillRect(0,0,dw,dh);
    drawHellflash();
    if (doomShakeT > 0){ dctx.restore(); }
  }
  function spawnPrime(){
    // Create a Prime variant based on a warden template
    const base = demons[Math.floor(Math.random()*demons.length)] || { x:dw/2, y:dh/2 };
    const d = {
      x: clamp(base.x + rand(-120,120), 60, dw-60), y: clamp(base.y + rand(-120,120), 60, dh-60),
      vx: 0, vy: 0,
      size: rand(110, 140), spin: 0, angle: 0, spikes: 24,
      spikesVar: new Array(24).fill(0).map(()=> rand(0.8, 1.4)),
      cracks: new Array(5).fill(0).map(()=> ({ a: rand(0,Math.PI*2), l: rand(0.5, 1.0) })),
      bobPhase: Math.random()*Math.PI*2, bobSpeed: rand(0.001, 0.003),
      eyePhase: 0, eyeSpeed: rand(0.004, 0.008), hue: rand(0,12),
      jitterT: 0, jitterEvery: Math.floor(rand(40, 90)),
      tx: 0, ty: 0, tLife: 0,
      maxSpeed: rand(0.7, 1.1), accel: rand(0.003, 0.006),
      lidBase: rand(0.34, 0.5), lidAmp: rand(0.1, 0.2), lidPhase: 0, lidSpeed: rand(0.003, 0.008),
      mouthPhase: 0, mouthSpeed: rand(0.006, 0.012), mouthBase: rand(0.14, 0.22), mouthAmp: rand(0.3, 0.45),
      lungeT: 0, lungeCd: Math.floor(rand(200, 500)),
  eyelets: [],
      beamT: 0, beamCd: Math.floor(rand(120, 300)),
      variant: 'prime'
    };
    // Initialize crown eyes properly
    const n = Math.floor(rand(12, 18));
    d.eyelets = [];
    for (let i=0;i<n;i++) d.eyelets.push({ ang: (i/n)*Math.PI*1.4 + rand(-0.2,0.2) - Math.PI*0.7, r: rand(0.5, 0.95), blinkPhase: Math.random()*Math.PI*2, blinkSpeed: rand(0.02, 0.05) });
    d.tx = d.x + rand(-dw*0.25, dw*0.25); d.ty = d.y + rand(-dh*0.25, dh*0.25); d.tLife = Math.floor(rand(140, 260));
    demons.push(d);
    playRoarFX(); const sf = doomReduced?0.6:1.0; doomShakeT = Math.max(doomShakeT, Math.floor(36*sf)); flashT = Math.floor(rand(10, 20)*sf);
  }

  if (prefersReduced) return; // Respect motion preference after wiring panel

  // Ambient audio rumble (starts on first interaction)
  let audioCtx = null, rumbleOsc = null, rumbleGain = null, audioStarted = false, masterGain = null, currentVolume = 0.55;
  let noiseBuffer = null;
  function ensureMaster(){
    if (!audioCtx) return null;
    if (!masterGain){ masterGain = audioCtx.createGain(); masterGain.gain.value = currentVolume; masterGain.connect(audioCtx.destination); }
    return masterGain;
  }
  function connectOut(node){ const mg = ensureMaster(); if (mg) node.connect(mg); else node.connect(audioCtx.destination); }
  function createNoise(){
    if (!audioCtx) return;
    const len = 2 * audioCtx.sampleRate;
    const buffer = audioCtx.createBuffer(1, len, audioCtx.sampleRate);
    const data = buffer.getChannelData(0);
    for (let i=0;i<len;i++) data[i] = Math.random()*2-1;
    noiseBuffer = buffer;
  }
  function envGain(gainNode, peak, attack, decay){
    const t = audioCtx.currentTime;
    gainNode.gain.cancelScheduledValues(t);
    gainNode.gain.setValueAtTime(0, t);
    gainNode.gain.linearRampToValueAtTime(peak, t+attack);
    gainNode.gain.exponentialRampToValueAtTime(0.0001, t+attack+decay);
  }
  function playSweep(f0, f1, dur, vol){
    if (!audioCtx) return;
    const osc = audioCtx.createOscillator();
    const g = audioCtx.createGain(); g.gain.value = 0;
    osc.type = 'triangle';
    osc.frequency.setValueAtTime(f0, audioCtx.currentTime);
    osc.frequency.exponentialRampToValueAtTime(f1, audioCtx.currentTime+dur);
    osc.connect(g); connectOut(g);
    envGain(g, vol, 0.01, dur*0.8);
    osc.start(); osc.stop(audioCtx.currentTime + dur + 0.2);
  }
  function playNoiseBurst(freq, q, dur, vol){
    if (!audioCtx || !noiseBuffer) return;
    const src = audioCtx.createBufferSource(); src.buffer = noiseBuffer; src.loop = false;
    const bp = audioCtx.createBiquadFilter(); bp.type = 'bandpass'; bp.frequency.value = freq; bp.Q.value = q;
    const g = audioCtx.createGain(); g.gain.value = 0;
    src.connect(bp); bp.connect(g); connectOut(g);
    envGain(g, vol, 0.005, dur);
    src.start(); src.stop(audioCtx.currentTime + dur + 0.1);
  }
  function playLungeFX(){
    // Deep fall + noise rasp
    try{
      playSweep(180, 60, 0.25, ultra?0.08:0.05);
      playNoiseBurst(220, 1.2, 0.2, ultra?0.05:0.03);
    }catch(e){}
  }
  function playSpitFX(){
    try{ playSweep(1200, 700, 0.08, 0.03); }catch(e){}
  }
  function playSplatFX(){
    try{ playNoiseBurst(160, 0.8, 0.12, 0.04); }catch(e){}
  }
  function playThunderFX(){
    try{
      playNoiseBurst(60, 0.7, 0.35, 0.08);
      playSweep(200, 90, 0.35, 0.08);
    }catch(e){}
  }
  function playRoarFX(){
    try{
      playNoiseBurst(140, 0.9, 0.5, 0.1);
      playSweep(120, 70, 0.45, 0.08);
    }catch(e){}
  }
  function startRumble(){
    if (audioStarted) return; audioStarted = true;
    try{
      const AC = window.AudioContext || window.webkitAudioContext;
      audioCtx = new AC();
      ensureMaster();
      rumbleGain = audioCtx.createGain();
      rumbleGain.gain.value = 0.02;
      rumbleOsc = audioCtx.createOscillator();
      rumbleOsc.type = 'sawtooth';
      rumbleOsc.frequency.value = 48; // low rumble
      // subtle detune LFO
      const lfo = audioCtx.createOscillator();
      lfo.type = 'sine'; lfo.frequency.value = 0.2;
      const lfoGain = audioCtx.createGain(); lfoGain.gain.value = 2;
      lfo.connect(lfoGain); lfoGain.connect(rumbleOsc.detune);
      rumbleOsc.connect(rumbleGain); connectOut(rumbleGain);
      rumbleOsc.start(); lfo.start();
      createNoise();
      // periodically pulse on lunges by raising gain briefly
      setInterval(()=>{
        if (!rumbleGain) return;
        const base = ultra ? 0.028 : 0.02;
        rumbleGain.gain.setTargetAtTime(base, audioCtx.currentTime, 0.4);
      }, 2000);
    }catch(e){ /* ignore if blocked */ }
  }
  doc.addEventListener('pointerdown', startRumble, { once:true });
  doc.addEventListener('keydown', startRumble, { once:true });

  // Glitch effect: jitter pseudo-layers on .glitch elements
  const glitchNodes = Array.from(doc.querySelectorAll('.glitch'));
  function hsl(h, s, l){ return `hsl(${(h%360+360)%360}, ${s}%, ${l}%)`; }
  function tick(){
    const t = performance.now();
    const strong = body.classList.contains('lights-on');
    for(const el of glitchNodes){
      const a = Math.sin(t/130 + el.offsetTop) * (strong ? 1.5 : 0.2);
      const b = Math.cos(t/170 + el.offsetLeft) * (strong ? 1.5 : 0.2);
      el.style.setProperty('--gx', a.toFixed(2)+'px');
      el.style.setProperty('--gy', b.toFixed(2)+'px');
      el.style.setProperty('--shadow-blue', `0 0 ${strong?10:0}px #00ffff, ${a}px ${b}px ${strong?24:0}px rgba(0,255,255,${strong?0.65:0})`);
      el.style.setProperty('--shadow-green', `${-a}px ${-b}px ${strong?8:0}px rgba(0,255,136,${strong?0.8:0})`);
    }
    // Rainbow: smoothly rotate accent hues
    if (body.classList.contains('theme-rainbow')){
      const base = (t/30) * rainbowSpeed % 360; // adjustable rotation
      setVar('--neon-blue', hsl(base+0, 100, 60));
      setVar('--neon-green', hsl(base+120, 100, 60));
      setVar('--neon-pink', hsl(base+240, 100, 60));
    }
    if (body.classList.contains('theme-matrix')){ drawMatrix(t); }
    if (body.classList.contains('theme-laser')){ drawLaser(t); }
    if (body.classList.contains('theme-alien-xmas')){ drawAlienSnow(t); }
    if (body.classList.contains('theme-doom')){ drawDoom(t); }
    requestAnimationFrame(tick);
  }

  // Random flicker class toggles
  const flickerables = doc.querySelectorAll('.nav-link, .button, .card, .site-title');
  function flicker(){
    if (!body.classList.contains('lights-on')) { setTimeout(flicker, 1200); return; }
    const el = flickerables[Math.floor(Math.random()*flickerables.length)];
    if (el){
      el.classList.add('flick');
      setTimeout(()=>el.classList.remove('flick'), 120 + Math.random()*280);
    }
    setTimeout(flicker, 600 + Math.random()*1400);
  }

  // Start loops
  requestAnimationFrame(tick);
  setTimeout(flicker, 800);

  // Doom controls/state integration and content warning gate
  (function(){
    const gate = doc.getElementById('doom-gate');
    const acceptKey = 'doom-gate-v1';
    const loadGate = () => { try{ return localStorage.getItem(acceptKey); }catch{ return null; } };
    const saveGate = (v) => { try{ localStorage.setItem(acceptKey, v); }catch{} };
    function applyDoomSettingsFromStore(){
      const ls = load();
      if (ls && (ls.dInt || ls.dVol != null || ls.dReduced != null)){
        // push into runtime
        ultra = (ls.dInt||'ultra') === 'ultra';
        doomReduced = !!ls.dReduced;
        currentVolume = (typeof ls.dVol==='number') ? clamp(ls.dVol, 0, 1) : currentVolume;
        // reflect in controls if present
        if (CP.dInt) CP.dInt.value = ultra?'ultra':'normal';
        if (CP.dVol) CP.dVol.value = String(currentVolume);
        if (CP.dReduced) CP.dReduced.checked = doomReduced;
      }
    }
    window.addEventListener('load', applyDoomSettingsFromStore);
    // When theme changes, if switching to Doom and no prior choice, show gate
    function maybeShowGate(){
      if (detectTheme() !== 'doom') return;
      if (loadGate()) return; // already accepted
      if (!gate) return;
      gate.classList.remove('is-hidden');
    }
    setTimeout(maybeShowGate, 50);
    function closeGate(){ if (gate) gate.classList.add('is-hidden'); }
    const btnUltra = doc.getElementById('doom-gate-ultra');
    const btnReduced = doc.getElementById('doom-gate-reduced');
    const btnDismiss = doc.getElementById('doom-gate-dismiss');
    btnUltra && btnUltra.addEventListener('click', ()=>{
      const ns = Object.assign({}, state(), { dInt:'ultra', dVol:0.6, dReduced:false });
      apply(ns); save(ns); saveGate('ok'); closeGate();
    });
    btnReduced && btnReduced.addEventListener('click', ()=>{
      const ns = Object.assign({}, state(), { dInt:'normal', dVol:0.3, dReduced:true });
      apply(ns); save(ns); saveGate('reduced'); closeGate();
    });
    btnDismiss && btnDismiss.addEventListener('click', ()=>{ saveGate('dismiss'); closeGate(); });

    // Hook apply to pull in doom fields
    const _apply = apply;
    apply = function(s){
      _apply(s);
      // Doom-specific
      if (s.dInt){ ultra = (s.dInt === 'ultra'); if (CP.dInt) CP.dInt.value = s.dInt; }
      if (typeof s.dVol === 'number'){ currentVolume = clamp(s.dVol, 0, 1); if (CP.dVol) CP.dVol.value = String(currentVolume); try{ if (masterGain) masterGain.gain.setTargetAtTime(currentVolume, audioCtx.currentTime, 0.1);}catch(e){} }
      if (typeof s.dReduced === 'boolean'){ doomReduced = s.dReduced; if (CP.dReduced) CP.dReduced.checked = doomReduced; }
      updateCPVisibility(s.theme);
    };
  })();
})();
