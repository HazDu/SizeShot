'use strict';

(() => {
  const $ = (s) => document.querySelector(s);
  const svg = $('#stage'), photo = $('#photo'), frame = $('#frame');
  const layer = $('#layer'), handlesG = $('#handles');
  const appEl = $('#app'), wrap = $('#wrap'), editor = $('#editor'), hintEl = $('#hint');

  const FONT = "'Segoe UI', Roboto, 'Helvetica Neue', Arial, sans-serif";
  const STORE = 'sizeshot.autosave.v1';
  const COLORS = ['#111111', '#FFFFFF', '#FFB020', '#FF4D4F', '#22C55E', '#38BDF8', '#A78BFA'];

  const TYPES = {
    dim:     { name: 'Dimension', text: true,  hint: 'Press at one end, drag across the object and release at the other end.' },
    callout: { name: 'Callout',   text: true,  hint: 'Press on the spot to point at, drag to where the label should sit.' },
    text:    { name: 'Text',      text: true,  hint: 'Click where the text should go.' },
    arrow:   { name: 'Arrow',     text: false, hint: 'Drag from the tail to the tip of the arrow.' },
    angle:   { name: 'Angle',     text: true,  hint: 'Press on the corner, drag along the first edge, then click on the second edge.' },
    rect:    { name: 'Box',       text: false, hint: 'Drag to outline an area. Hold Shift for a square.' },
    ellipse: { name: 'Circle',    text: false, hint: 'Drag to circle an area. Hold Shift for a perfect circle.' },
    marker:  { name: 'Marker',    text: true,  hint: 'Click to drop a numbered marker. Numbers count up automatically.' },
  };
  const SELECT_HINT = 'Click a shape to select it · drag handles to reshape · double-click to edit text · scroll to zoom';
  const PLACEHOLDER = { dim: 'e.g. 120 cm', callout: 'Label', text: 'Type here', marker: '#' };
  const LINE_TYPES = ['dim', 'callout', 'arrow', 'angle', 'rect', 'ellipse'];

  // ---------- state ----------
  let doc = { image: null, w: 0, h: 0, items: [] };
  let B = 1;                       // base unit: scales default sizes with the image resolution
  let view = { x: 0, y: 0, w: 1, h: 1 };
  let pu = 1;                      // image units per screen pixel
  let tool = 'select';
  let selId = null;
  let drag = null;
  let creating = null;
  let editing = null;
  let spaceDown = false;
  let exporting = false;
  let geom = {};                   // label boxes from the last render, by item id
  let hist = [], hIdx = -1;
  const LABEL_DEFAULTS = { bg: 'auto', tc: 'auto', bc: 'auto', bw: 0.6, pad: 0.8, rad: 0.25 };
  const defaults = { color: COLORS[0], lw: 1, fs: 0.6, dash: false, fill: false, ...LABEL_DEFAULTS };

  // ---------- helpers ----------
  const V = {
    add: (a, b) => ({ x: a.x + b.x, y: a.y + b.y }),
    sub: (a, b) => ({ x: a.x - b.x, y: a.y - b.y }),
    mul: (a, k) => ({ x: a.x * k, y: a.y * k }),
    len: (a) => Math.hypot(a.x, a.y),
    dot: (a, b) => a.x * b.x + a.y * b.y,
    unit: (a) => { const l = Math.hypot(a.x, a.y) || 1; return { x: a.x / l, y: a.y / l }; },
    perp: (a) => ({ x: -a.y, y: a.x }),
    mid: (a, b) => ({ x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 }),
  };
  const f = (n) => Math.round(n * 100) / 100;
  const P = (p) => `${f(p.x)} ${f(p.y)}`;
  const esc = (s) => String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
  const uid = () => Math.random().toString(36).slice(2, 10);
  const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
  const byId = (id) => doc.items.find((i) => i.id === id);
  const sel = () => (selId ? byId(selId) : null);
  const mctx = document.createElement('canvas').getContext('2d');
  const measure = (t, size) => { mctx.font = `600 ${size}px ${FONT}`; return mctx.measureText(t).width; };

  function lum(hex) {
    const n = parseInt(hex.slice(1), 16);
    return (0.2126 * (n >> 16 & 255) + 0.7152 * (n >> 8 & 255) + 0.0722 * (n & 255)) / 255;
  }
  const ink = (c) => (lum(c) > 0.55 ? '#111111' : '#FFFFFF');
  const haloOf = (c) => (lum(c) > 0.3 ? 'rgba(0,0,0,0.55)' : 'rgba(255,255,255,0.8)');
  const LW = (it) => 3 * B * it.lw;
  const FS = (it) => 26 * B * it.fs;
  const AH = (it) => LW(it) * 3 + 9 * B;
  const upright = (deg) => (deg > 90 ? deg - 180 : deg <= -90 ? deg + 180 : deg);

  function snapAngle(p, anchor) {
    const d = V.sub(p, anchor), r = V.len(d), step = Math.PI / 12;
    const a = Math.round(Math.atan2(d.y, d.x) / step) * step;
    return { x: anchor.x + Math.cos(a) * r, y: anchor.y + Math.sin(a) * r };
  }

  // ---------- drawing ----------
  // Collects border (outline) strokes, main strokes, invisible hit areas and labels so
  // that the border never paints over the colored lines of the same shape.
  function painter(it) {
    const lw = LW(it), col = it.color;
    const hc = it.bc === 'auto' ? haloOf(col) : it.bc;
    const ol = hc === 'none' ? 0 : lw * 0.6 * it.bw;   // border width on each side of a line
    const H = [], M = [], hits = [], top = [];
    const dashA = it.dash ? ` stroke-dasharray="${f(lw * 3)} ${f(lw * 2.4)}"` : '';
    const cap = ' stroke-linecap="round" stroke-linejoin="round"';
    return {
      line(d, dashable = true) {
        const da = dashable ? dashA : '';
        if (ol) H.push(`<path d="${d}" fill="none" stroke="${hc}" stroke-width="${f(lw + ol * 2)}"${cap}${da}/>`);
        M.push(`<path d="${d}" fill="none" stroke="${col}" stroke-width="${f(lw)}"${cap}${da}/>`);
        hits.push(d);
      },
      area(d) { M.unshift(`<path d="${d}" fill="${col}" fill-opacity="0.22"/>`); },
      head(tip, dir) {
        const ah = AH(it), n = V.perp(dir), base = V.sub(tip, V.mul(dir, ah));
        const d = `M${P(tip)}L${P(V.add(base, V.mul(n, ah * 0.42)))}L${P(V.sub(base, V.mul(n, ah * 0.42)))}Z`;
        if (ol) H.push(`<path d="${d}" fill="${hc}" stroke="${hc}" stroke-width="${f(ol * 2)}" stroke-linejoin="round"/>`);
        M.push(`<path d="${d}" fill="${col}" stroke="${col}" stroke-width="${f(lw * 0.3)}" stroke-linejoin="round"/>`);
      },
      dot(c, r) {
        if (ol) H.push(`<circle cx="${f(c.x)}" cy="${f(c.y)}" r="${f(r + ol)}" fill="${hc}"/>`);
        M.push(`<circle cx="${f(c.x)}" cy="${f(c.y)}" r="${f(r)}" fill="${col}"/>`);
      },
      top(s) { top.push(s); },
      out() {
        const hw = f(Math.max(lw * 3, 14 * pu));
        const hs = exporting ? '' : hits.map((d) => `<path d="${d}" fill="none" stroke="transparent" stroke-width="${hw}" stroke-linecap="round"/>`).join('');
        return H.join('') + M.join('') + hs + top.join('');
      },
    };
  }

  // Resolved label-box style; 'auto' values follow the shape color. Without a background
  // the border outlines the letters themselves instead of the box.
  function boxStyle(it) {
    const fs = FS(it);
    const bg = it.bg === 'auto' ? it.color : it.bg;
    const tc = it.tc === 'auto' ? (bg === 'none' ? it.color : ink(bg)) : it.tc;
    const bc = it.bc === 'auto' ? haloOf(bg === 'none' ? tc : bg) : it.bc;
    const bw = bc === 'none' || it.bw <= 0 ? 0 : bg === 'none' ? fs * 0.16 * it.bw : Math.max(0.5, fs * 0.07 * it.bw);
    return { fs, bg, bc, tc, bw, padX: fs * (0.12 + 0.36 * it.pad), padY: fs * (0.1 + 0.32 * it.pad) };
  }

  // Lays out lines so the visible glyphs are centered on (0,0): horizontally by
  // their ink bounds, vertically by cap height (descenders hang below, as in UI type).
  let capRatio = 0;
  function textBlock(lines, fs) {
    mctx.font = `600 ${fs}px ${FONT}`;
    if (!capRatio) capRatio = mctx.measureText('H').actualBoundingBoxAscent / fs || 0.7;
    const lh = fs * 1.22, cap = capRatio * fs, n = lines.length;
    const rows = lines.map((l, i) => {
      const m = mctx.measureText(l), L = m.actualBoundingBoxLeft || 0, R = m.actualBoundingBoxRight || 0;
      return { l, w: l.trim() ? L + R : 0, x: (L - R) / 2, y: (i - (n - 1) / 2) * lh + cap / 2 };
    });
    return { rows, w: Math.max(0, ...rows.map((r) => r.w)), h: (n - 1) * lh + cap };
  }

  function textMarkup(blk, fs, st, ox = 0, oy = 0) {
    const halo = st.bg === 'none' && st.bw
      ? ` stroke="${st.bc}" stroke-width="${f(st.bw)}" stroke-linejoin="round" paint-order="stroke"` : '';
    return blk.rows.map((r) => `<text x="${f(ox + r.x)}" y="${f(oy + r.y)}" font-size="${f(fs)}" fill="${st.tc}"${halo}>${esc(r.l)}</text>`).join('');
  }

  function labelSize(it, text) {
    const st = boxStyle(it), blk = textBlock(String(text).split('\n'), st.fs);
    return { st, blk, w: Math.max(blk.w, st.fs * 0.5) + st.padX * 2, h: blk.h + st.padY * 2 };
  }

  function label(it, c, ang, text) {
    const { st, blk, w, h } = labelSize(it, text), fs = st.fs;
    geom[it.id] = { x: c.x, y: c.y, w, h, ang };
    const rx = f(clamp(it.rad, 0, 1) * Math.min(w, h) / 2);
    const fill = st.bg === 'none' ? 'transparent' : st.bg;
    const stroke = st.bw && st.bg !== 'none' ? ` stroke="${st.bc}" stroke-width="${f(st.bw)}"` : '';
    return `<g transform="translate(${P(c)}) rotate(${f(ang)})">` +
      `<rect x="${f(-w / 2)}" y="${f(-h / 2)}" width="${f(w)}" height="${f(h)}" rx="${rx}" fill="${fill}"${stroke}/>` +
      textMarkup(blk, fs, st) + '</g>';
  }

  function dimGeometry(it) {
    const [a, b] = it.pts, u = V.unit(V.sub(b, a)), n = V.perp(u), o = it.off || 0;
    return { a, b, u, n, q1: V.add(a, V.mul(n, o)), q2: V.add(b, V.mul(n, o)) };
  }

  function angleInfo(it) {
    const [v, a, b] = it.pts, da = V.sub(a, v), db = V.sub(b, v);
    const t1 = Math.atan2(da.y, da.x), t2 = Math.atan2(db.y, db.x);
    let diff = t2 - t1;
    while (diff > Math.PI) diff -= 2 * Math.PI;
    while (diff <= -Math.PI) diff += 2 * Math.PI;
    return { v, da, db, t1, diff, deg: Math.round(Math.abs(diff) * 180 / Math.PI) };
  }

  const RENDER = {
    dim(it, p) {
      const { a, b, u, n, q1, q2 } = dimGeometry(it);
      const L = V.len(V.sub(b, a));
      if (L < 0.5) return;
      const o = it.off || 0, ah = AH(it), lw = LW(it);
      if (Math.abs(o) > lw * 2) {
        const s = Math.sign(o), gap = V.mul(n, s * lw * 1.5), ext = V.mul(n, s * ah * 0.5);
        p.line(`M${P(V.add(a, gap))}L${P(V.add(q1, ext))}M${P(V.add(b, gap))}L${P(V.add(q2, ext))}`, false);
      }
      const tk = V.mul(n, ah * 0.75);
      p.line(`M${P(V.sub(q1, tk))}L${P(V.add(q1, tk))}M${P(V.sub(q2, tk))}L${P(V.add(q2, tk))}`, false);
      if (L > ah * 2.6) {
        p.line(`M${P(V.add(q1, V.mul(u, ah * 0.6)))}L${P(V.sub(q2, V.mul(u, ah * 0.6)))}`);
        p.head(q1, V.mul(u, -1));
        p.head(q2, u);
      } else {
        // too short for inside arrows: point at the ticks from outside
        p.line(`M${P(V.sub(q1, V.mul(u, ah * 2)))}L${P(V.add(q2, V.mul(u, ah * 2)))}`);
        p.head(q1, u);
        p.head(q2, V.mul(u, -1));
      }
      if (!it.text) return;
      let c = V.mid(q1, q2);
      const box = labelSize(it, it.text);
      if (box.w > L - ah * 2.2) {
        // label doesn't fit between the arrows: put it beside the line, away from the object
        c = V.add(c, V.mul(n, (o < 0 ? -1 : 1) * (box.h / 2 + ah * 0.9)));
      }
      p.top(label(it, c, upright(Math.atan2(u.y, u.x) * 180 / Math.PI), it.text));
    },
    callout(it, p) {
      const [t, s] = it.pts, d = V.sub(t, s), ah = AH(it);
      if (V.len(d) > ah * 1.2) {
        const u = V.unit(d);
        p.line(`M${P(s)}L${P(V.sub(t, V.mul(u, ah * 0.6)))}`);
        p.head(t, u);
      }
      if (it.text) p.top(label(it, s, 0, it.text));
      else p.dot(s, LW(it) * 1.6);
    },
    text(it, p) {
      p.top(label(it, it.pts[0], 0, it.text || ' '));
    },
    arrow(it, p) {
      const [a, b] = it.pts, d = V.sub(b, a);
      if (V.len(d) < 0.5) return;
      const u = V.unit(d);
      p.line(`M${P(a)}L${P(V.sub(b, V.mul(u, AH(it) * 0.6)))}`);
      p.head(b, u);
    },
    angle(it, p) {
      const [v, a, b] = it.pts;
      p.line(`M${P(a)}L${P(v)}L${P(b)}`);
      const { da, db, t1, diff, deg } = angleInfo(it);
      if (V.len(da) < 1 || V.len(db) < 1 || Math.abs(diff) < 0.002) return;
      const r = Math.max(12 * B, Math.min(V.len(da), V.len(db)) * 0.32);
      const e1 = { x: v.x + Math.cos(t1) * r, y: v.y + Math.sin(t1) * r };
      const e2 = { x: v.x + Math.cos(t1 + diff) * r, y: v.y + Math.sin(t1 + diff) * r };
      p.line(`M${P(e1)}A${f(r)} ${f(r)} 0 0 ${diff > 0 ? 1 : 0} ${P(e2)}`, false);
      const tm = t1 + diff / 2, dist = r + FS(it) * 1.3;
      p.top(label(it, { x: v.x + Math.cos(tm) * dist, y: v.y + Math.sin(tm) * dist }, 0, it.text || `${deg}°`));
    },
    rect(it, p) {
      const [a, b] = it.pts, x = Math.min(a.x, b.x), y = Math.min(a.y, b.y);
      const w = Math.abs(b.x - a.x), h = Math.abs(b.y - a.y);
      const d = `M${f(x)} ${f(y)}h${f(w)}v${f(h)}h${f(-w)}Z`;
      if (it.fill) p.area(d);
      p.line(d);
    },
    ellipse(it, p) {
      const [a, b] = it.pts, c = V.mid(a, b), rx = Math.abs(b.x - a.x) / 2, ry = Math.abs(b.y - a.y) / 2;
      const d = `M${f(c.x - rx)} ${f(c.y)}a${f(rx)} ${f(ry)} 0 1 0 ${f(2 * rx)} 0a${f(rx)} ${f(ry)} 0 1 0 ${f(-2 * rx)} 0Z`;
      if (it.fill) p.area(d);
      p.line(d);
    },
    marker(it, p) {
      const c = it.pts[0], st = boxStyle(it), blk = textBlock([it.text || ''], st.fs);
      const r = Math.max(blk.h / 2, blk.w / 2) + st.padY + st.fs * 0.08;
      geom[it.id] = { x: c.x, y: c.y, w: r * 2, h: r * 2, ang: 0 };
      const stroke = st.bw && st.bg !== 'none' ? ` stroke="${st.bc}" stroke-width="${f(st.bw)}"` : '';
      p.top(`<circle cx="${f(c.x)}" cy="${f(c.y)}" r="${f(r)}" fill="${st.bg === 'none' ? 'transparent' : st.bg}"${stroke}/>` +
        textMarkup(blk, st.fs, st, c.x, c.y));
    },
  };

  function itemsMarkup(forExport) {
    exporting = forExport;
    geom = {};
    const out = doc.items.map((it) => {
      const p = painter(it);
      RENDER[it.type](it, p);
      return `<g data-id="${it.id}">${p.out()}</g>`;
    }).join('');
    exporting = false;
    return out;
  }

  function handlesOf(it) {
    const p = it.pts;
    switch (it.type) {
      case 'dim': {
        const { a, b, n } = dimGeometry(it);
        const q = V.add(V.add(a, V.mul(V.sub(b, a), 0.25)), V.mul(n, it.off || 0));
        return [{ k: 'p0', ...p[0] }, { k: 'p1', ...p[1] }, { k: 'off', ...q, diamond: true }];
      }
      case 'callout': case 'arrow': return [{ k: 'p0', ...p[0] }, { k: 'p1', ...p[1] }];
      case 'angle': return [{ k: 'p0', ...p[0] }, { k: 'p1', ...p[1] }, { k: 'p2', ...p[2] }];
      case 'rect': case 'ellipse': {
        const [a, b] = p;
        return [{ k: 'c0', x: a.x, y: a.y }, { k: 'c1', x: b.x, y: a.y }, { k: 'c2', x: b.x, y: b.y }, { k: 'c3', x: a.x, y: b.y }];
      }
      default: return [];
    }
  }

  function renderHandles() {
    const it = sel();
    if (!it || (creating && creating.item === it)) { handlesG.innerHTML = ''; return; }
    let s = '';
    const g = geom[it.id];
    if (g && ['text', 'marker', 'callout'].includes(it.type)) {
      const pad = 4 * pu;
      s += `<rect class="outline" x="${f(g.x - g.w / 2 - pad)}" y="${f(g.y - g.h / 2 - pad)}" width="${f(g.w + pad * 2)}" height="${f(g.h + pad * 2)}" rx="${f(4 * pu)}" stroke-width="${f(1.5 * pu)}" stroke-dasharray="${f(4 * pu)} ${f(3 * pu)}" transform="rotate(${f(g.ang)} ${f(g.x)} ${f(g.y)})"/>`;
    }
    const r = 6.5 * pu, sw = f(2 * pu);
    for (const h of handlesOf(it)) {
      s += h.diamond
        ? `<rect class="h" data-id="${it.id}" data-h="${h.k}" x="${f(h.x - r * 0.8)}" y="${f(h.y - r * 0.8)}" width="${f(r * 1.6)}" height="${f(r * 1.6)}" transform="rotate(45 ${f(h.x)} ${f(h.y)})" stroke-width="${sw}"><title>Drag to offset the dimension line</title></rect>`
        : `<circle class="h" data-id="${it.id}" data-h="${h.k}" cx="${f(h.x)}" cy="${f(h.y)}" r="${f(r)}" stroke-width="${sw}"/>`;
    }
    handlesG.innerHTML = s;
  }

  function render() {
    if (!doc.image) return;
    svg.setAttribute('viewBox', `${view.x} ${view.y} ${view.w} ${view.h}`);
    const ctm = svg.getScreenCTM();
    if (ctm && ctm.a) pu = 1 / ctm.a;
    layer.innerHTML = itemsMarkup(false);
    renderHandles();
    $('#zVal').textContent = `${Math.round(100 / pu)}%`;
    positionEditor();
  }

  // ---------- view ----------
  function fit() {
    const pad = 0.04;
    view = { x: -doc.w * pad, y: -doc.h * pad, w: doc.w * (1 + 2 * pad), h: doc.h * (1 + 2 * pad) };
    render();
  }
  function zoomAt(p, factor) {
    const scale = clamp((1 / pu) * factor, 0.03, 16);
    factor = scale * pu;
    view.x = p.x - (p.x - view.x) / factor;
    view.y = p.y - (p.y - view.y) / factor;
    view.w /= factor;
    view.h /= factor;
    render();
  }
  const viewCenter = () => ({ x: view.x + view.w / 2, y: view.y + view.h / 2 });

  function toImg(e) {
    const m = svg.getScreenCTM().inverse();
    const p = new DOMPoint(e.clientX, e.clientY).matrixTransform(m);
    return { x: p.x, y: p.y };
  }
  function toScreen(p) {
    const m = svg.getScreenCTM();
    const q = new DOMPoint(p.x, p.y).matrixTransform(m);
    return { x: q.x, y: q.y };
  }

  // ---------- history & persistence ----------
  const snapshot = () => JSON.stringify(doc.items);
  function resetHistory() { hist = [snapshot()]; hIdx = 0; updButtons(); }
  function commit() {
    const s = snapshot();
    if (s !== hist[hIdx]) {
      hist.splice(hIdx + 1);
      hist.push(s);
      if (hist.length > 300) hist.shift();
      hIdx = hist.length - 1;
    }
    updButtons();
    scheduleSave();
  }
  function restore(i) {
    if (i < 0 || i >= hist.length) return;
    hIdx = i;
    doc.items = JSON.parse(hist[hIdx]);
    if (!sel()) selId = null;
    render(); syncProps(); updButtons(); scheduleSave();
  }
  const undo = () => { if (editing) finishEdit(true); if (creating) cancelCreate(); restore(hIdx - 1); };
  const redo = () => restore(hIdx + 1);

  function updButtons() {
    $('#btnUndo').disabled = hIdx <= 0;
    $('#btnRedo').disabled = hIdx >= hist.length - 1;
    document.querySelectorAll('.needs-image').forEach((b) => { b.disabled = !doc.image; });
  }

  let saveTimer = null, warnedQuota = false;
  function scheduleSave() {
    clearTimeout(saveTimer);
    saveTimer = setTimeout(() => {
      try {
        localStorage.setItem(STORE, JSON.stringify(doc));
      } catch (err) {
        try { localStorage.removeItem(STORE); } catch (e) { /* storage unavailable */ }
        if (!warnedQuota) { warnedQuota = true; toast('Image is too large for autosave. Use Save to keep your work.'); }
      }
    }, 400);
  }

  // ---------- image loading ----------
  function setImage(url, items, initialSelect) {
    const img = new Image();
    img.onload = () => {
      doc = { image: url, w: img.naturalWidth, h: img.naturalHeight, items: (items || []).map(normalize) };
      B = Math.max(0.8, Math.max(doc.w, doc.h) / 1000);
      photo.setAttribute('href', url);
      for (const el of [photo, frame]) { el.setAttribute('width', doc.w); el.setAttribute('height', doc.h); }
      appEl.classList.add('has-image');
      appEl.classList.remove('no-image');
      selId = initialSelect || null;
      creating = null; drag = null;
      setTool('select');
      fit();
      resetHistory();
      syncProps();
      scheduleSave();
    };
    img.onerror = () => toast('Could not read that image.');
    img.src = url;
  }

  function loadFile(file) {
    if (!file) return;
    const isJson = file.type === 'application/json' || /\.json$/i.test(file.name);
    if (!isJson && !file.type.startsWith('image/')) { toast('Please choose an image file.'); return; }
    if (!isJson && doc.items.length && !confirm('Load a new image? Your current annotations will be removed (use Save first to keep them).')) return;
    const r = new FileReader();
    r.onload = () => {
      if (!isJson) { setImage(r.result); return; }
      try {
        const d = JSON.parse(r.result);
        if (!d.image || !Array.isArray(d.items)) throw new Error('bad file');
        setImage(d.image, d.items);
      } catch (err) {
        toast('That file is not a SizeShot project.');
      }
    };
    if (isJson) r.readAsText(file); else r.readAsDataURL(file);
  }

  // ---------- items ----------
  function newItem(type, pts) {
    return {
      id: uid(), type, pts: pts.map((p) => ({ x: p.x, y: p.y })),
      text: type === 'marker' ? nextMarker() : '',
      color: defaults.color, lw: defaults.lw, fs: defaults.fs, dash: defaults.dash,
      fill: type === 'rect' || type === 'ellipse' ? defaults.fill : false,
      off: 0,
      bg: type === 'text' && defaults.bg === 'auto' ? 'none' : defaults.bg,
      tc: defaults.tc, bc: defaults.bc, bw: defaults.bw, pad: defaults.pad, rad: defaults.rad,
    };
  }
  // fills in label style for items saved by older versions
  function normalize(it) {
    if (it.bg === undefined) it.bg = it.type === 'text' && !it.fill ? 'none' : 'auto';
    for (const k in LABEL_DEFAULTS) if (it[k] === undefined) it[k] = LABEL_DEFAULTS[k];
    return it;
  }
  function nextMarker() {
    const nums = doc.items.filter((i) => i.type === 'marker').map((i) => parseInt(i.text, 10)).filter((n) => !isNaN(n));
    return String(nums.length ? Math.max(...nums) + 1 : 1);
  }
  function deleteSelected() {
    if (!selId) return;
    doc.items = doc.items.filter((i) => i.id !== selId);
    selId = null;
    render(); syncProps(); commit();
  }
  function duplicateSelected() {
    const it = sel();
    if (!it) return;
    const c = JSON.parse(JSON.stringify(it));
    c.id = uid();
    c.pts = c.pts.map((p) => ({ x: p.x + 24 * B, y: p.y + 24 * B }));
    if (c.type === 'marker') c.text = nextMarker();
    doc.items.push(c);
    selId = c.id;
    render(); syncProps(); commit();
  }
  function bringToFront() {
    const it = sel();
    if (!it) return;
    doc.items = doc.items.filter((i) => i !== it).concat(it);
    render(); commit();
  }

  function dragHandle(it, k, p, shift) {
    if (k[0] === 'p') {
      const i = +k.slice(1);
      const anchor = it.type === 'angle' ? (i > 0 ? it.pts[0] : null) : it.pts[1 - i];
      if (shift && anchor) p = snapAngle(p, anchor);
      it.pts[i] = { x: p.x, y: p.y };
    } else if (k === 'off') {
      const n = V.perp(V.unit(V.sub(it.pts[1], it.pts[0])));
      it.off = V.dot(V.sub(p, it.pts[0]), n);
    } else {
      const [a, b] = it.pts, i = +k[1];
      if (i === 0) { a.x = p.x; a.y = p.y; }
      if (i === 1) { b.x = p.x; a.y = p.y; }
      if (i === 2) { b.x = p.x; b.y = p.y; }
      if (i === 3) { a.x = p.x; b.y = p.y; }
    }
  }

  // ---------- creation ----------
  const CLICK_DEFAULTS = { dim: [180, 0], callout: [120, -100], arrow: [-130, -100], rect: [180, 120], ellipse: [180, 120] };

  function startCreate(p, e) {
    const t = tool;
    if (t === 'text' || t === 'marker') {
      const it = newItem(t, [p]);
      doc.items.push(it);
      selId = it.id;
      setTool('select');
      render(); syncProps();
      if (t === 'text') startEdit(it, true); else commit();
      return;
    }
    const it = newItem(t, t === 'angle' ? [p, p, p] : [p, p]);
    doc.items.push(it);
    selId = it.id;
    creating = { item: it, phase: 1 };
    drag = { mode: 'create', sx: e.clientX, sy: e.clientY, moved: false };
    render();
  }

  function createMove(p, e) {
    const it = creating.item;
    if (Math.hypot(e.clientX - drag.sx, e.clientY - drag.sy) > 4) drag.moved = true;
    if (e.shiftKey) {
      if (it.type === 'rect' || it.type === 'ellipse') {
        const d = V.sub(p, it.pts[0]), m = Math.max(Math.abs(d.x), Math.abs(d.y));
        p = { x: it.pts[0].x + Math.sign(d.x || 1) * m, y: it.pts[0].y + Math.sign(d.y || 1) * m };
      } else {
        p = snapAngle(p, it.pts[0]);
      }
    }
    it.pts[1] = p;
    if (it.type === 'angle') it.pts[2] = { ...p };
  }

  function createRelease() {
    const it = creating.item;
    if (!drag.moved) {
      const o = it.type === 'angle' ? [180, 0] : CLICK_DEFAULTS[it.type];
      const v = { x: o[0] * B, y: o[1] * B };
      if (it.type === 'arrow') { it.pts[1] = { ...it.pts[0] }; it.pts[0] = V.add(it.pts[0], v); }
      else it.pts[1] = V.add(it.pts[0], v);
      if (it.type === 'angle') it.pts[2] = { ...it.pts[1] };
    }
    drag = null;
    if (it.type === 'angle') {
      creating.phase = 2;
      hintEl.textContent = 'Now click on the second edge of the angle (Esc to cancel).';
      render();
      return;
    }
    finishCreate();
  }

  function finishCreate() {
    const it = creating.item;
    creating = null;
    selId = it.id;
    setTool('select');
    render(); syncProps();
    if (it.type === 'dim' || it.type === 'callout') startEdit(it, true);
    else commit();
  }

  function cancelCreate() {
    if (!creating) return;
    doc.items = doc.items.filter((i) => i !== creating.item);
    creating = null; drag = null; selId = null;
    setTool(tool);
    render(); syncProps();
  }

  // ---------- inline text editor ----------
  function anchorOf(it) {
    const g = geom[it.id];
    if (g) return { x: g.x, y: g.y };
    if (it.type === 'dim') { const { q1, q2 } = dimGeometry(it); return V.mid(q1, q2); }
    if (it.type === 'callout') return it.pts[1];
    return it.pts[0];
  }

  function startEdit(it, isNew) {
    if (!TYPES[it.type].text) return;
    editing = { id: it.id, before: it.text, isNew };
    editor.value = it.text;
    editor.placeholder = it.type === 'angle' ? `${angleInfo(it).deg}° (auto)` : PLACEHOLDER[it.type];
    editor.hidden = false;
    sizeEditor();
    positionEditor();
    editor.focus();
    editor.select();
  }

  function sizeEditor() {
    const it = editing && byId(editing.id);
    if (!it) return;
    const fsPx = clamp(FS(it) / pu, 15, 42);
    const lines = (editor.value || editor.placeholder).split('\n');
    const w = Math.max(...lines.map((l) => measure(l, fsPx)));
    editor.style.fontSize = `${fsPx}px`;
    editor.style.width = `${Math.ceil(w + fsPx * 1.6 + 24)}px`;
    editor.rows = Math.max(1, editor.value.split('\n').length);
  }

  function positionEditor() {
    if (!editing) return;
    const it = byId(editing.id);
    if (!it) return;
    const s = toScreen(anchorOf(it));
    editor.style.left = `${s.x}px`;
    editor.style.top = `${s.y}px`;
  }

  function finishEdit(ok) {
    if (!editing) return;
    const ed = editing;
    editing = null;
    editor.hidden = true;
    const it = byId(ed.id);
    if (it) {
      if (!ok) it.text = ed.before;
      if (it.type === 'text' && !it.text.trim()) {
        doc.items = doc.items.filter((i) => i !== it);
        if (selId === it.id) selId = null;
      }
    }
    render(); syncProps(); commit();
  }

  editor.addEventListener('input', () => {
    const it = editing && byId(editing.id);
    if (!it) return;
    it.text = editor.value;
    sizeEditor();
    render();
    if (selId === it.id) $('#propText').value = it.text;
  });
  editor.addEventListener('keydown', (e) => {
    e.stopPropagation();
    if (e.key === 'Enter' && !e.shiftKey) { e.preventDefault(); finishEdit(true); }
    else if (e.key === 'Escape') { e.preventDefault(); finishEdit(false); }
  });
  editor.addEventListener('blur', () => finishEdit(true));

  // ---------- pointer interaction ----------
  svg.addEventListener('pointerdown', (e) => {
    if (!doc.image || e.button === 2) return;
    e.preventDefault();
    if (document.activeElement && document.activeElement !== document.body) document.activeElement.blur();
    if (editing) finishEdit(true);
    svg.setPointerCapture(e.pointerId);
    const p = toImg(e);

    if (e.button === 1 || spaceDown) {
      drag = { mode: 'pan', sx: e.clientX, sy: e.clientY, view: { ...view } };
      wrap.classList.add('panning');
      return;
    }
    if (creating && creating.phase === 2) {
      creating.item.pts[2] = e.shiftKey ? snapAngle(p, creating.item.pts[0]) : p;
      finishCreate();
      return;
    }
    const hEl = e.target.closest('[data-h]');
    if (hEl) {
      drag = { mode: 'handle', id: hEl.dataset.id, key: hEl.dataset.h, moved: false };
      return;
    }
    if (tool === 'select') {
      const iEl = e.target.closest('#layer > g[data-id]');
      if (iEl) {
        selId = iEl.dataset.id;
        render(); syncProps();
        drag = { mode: 'move', id: selId, last: p, moved: false };
      } else {
        if (selId) { selId = null; render(); syncProps(); }
        drag = { mode: 'pan', sx: e.clientX, sy: e.clientY, view: { ...view } };
        wrap.classList.add('panning');
      }
      return;
    }
    startCreate(p, e);
  });

  svg.addEventListener('pointermove', (e) => {
    if (!doc.image) return;
    if (creating && creating.phase === 2) {
      const p = toImg(e);
      creating.item.pts[2] = e.shiftKey ? snapAngle(p, creating.item.pts[0]) : p;
      render();
      return;
    }
    if (!drag) return;
    if (drag.mode === 'pan') {
      view.x = drag.view.x - (e.clientX - drag.sx) * pu;
      view.y = drag.view.y - (e.clientY - drag.sy) * pu;
      render();
      return;
    }
    const p = toImg(e);
    if (drag.mode === 'create') {
      createMove(p, e);
    } else if (drag.mode === 'move') {
      const it = byId(drag.id), d = V.sub(p, drag.last);
      it.pts = it.pts.map((q) => V.add(q, d));
      drag.last = p;
      drag.moved = true;
    } else if (drag.mode === 'handle') {
      dragHandle(byId(drag.id), drag.key, p, e.shiftKey);
      drag.moved = true;
    }
    render();
  });

  function pointerEnd() {
    if (!drag) return;
    if (drag.mode === 'create') { createRelease(); return; }
    const moved = drag.moved;
    wrap.classList.toggle('panning', spaceDown);
    drag = null;
    if (moved) commit();
  }
  svg.addEventListener('pointerup', pointerEnd);
  svg.addEventListener('pointercancel', pointerEnd);

  svg.addEventListener('dblclick', (e) => {
    const iEl = e.target.closest('#layer > g[data-id]');
    const it = iEl && byId(iEl.dataset.id);
    if (it) { selId = it.id; render(); syncProps(); startEdit(it, false); }
  });

  svg.addEventListener('wheel', (e) => {
    if (!doc.image) return;
    e.preventDefault();
    const dy = e.deltaMode === 1 ? e.deltaY * 16 : e.deltaY;
    zoomAt(toImg(e), Math.exp(-dy * 0.0015));
  }, { passive: false });

  window.addEventListener('resize', render);

  // ---------- tools ----------
  function setTool(t) {
    if (creating && t !== tool) cancelCreate();
    tool = t;
    document.querySelectorAll('.tool').forEach((b) => b.classList.toggle('active', b.dataset.tool === t));
    wrap.classList.toggle('mode-select', t === 'select');
    wrap.classList.toggle('mode-create', t !== 'select');
    hintEl.textContent = t === 'select' ? SELECT_HINT : TYPES[t].hint;
  }
  document.querySelectorAll('.tool').forEach((b) => b.addEventListener('click', () => {
    if (editing) finishEdit(true);
    setTool(b.dataset.tool);
  }));

  // ---------- properties panel ----------
  const propText = $('#propText'), propLw = $('#propLw'), propDash = $('#propDash'), propFill = $('#propFill');
  const RANGES = { fs: '#propFs', bw: '#propBw', pad: '#propPad', rad: '#propRad' };
  const OUTPUTS = { bw: ['#oBw', (v) => (v > 0 ? `${v.toFixed(1)}×` : 'none')], pad: ['#oPad', (v) => `${v.toFixed(2)}×`], rad: ['#oRad', (v) => `${Math.round(v * 100)}%`] };
  const SWATCHES = { color: ['#swColor', []], tc: ['#swTc', ['auto']], bg: ['#swBg', ['auto', 'none']], bc: ['#swBc', ['auto', 'none']] };
  const SPECIAL_TITLES = { auto: 'Automatic (matches the shape color)', none: 'None' };

  let activeTab = 'shape';
  $('#tabs').addEventListener('click', (e) => {
    const b = e.target.closest('[data-tab]');
    if (b) { activeTab = b.dataset.tab; syncProps(); }
  });

  const target = () => sel() || defaults;
  const show =(id, on) => $(id).classList.toggle('hidden', !on);

  for (const [key, [id, specials]] of Object.entries(SWATCHES)) {
    const el = $(id);
    el.innerHTML = specials.map((s) => `<button class="sw sw-${s}" data-c="${s}" title="${SPECIAL_TITLES[s]}"></button>`).join('') +
      COLORS.map((c) => `<button class="sw" data-c="${c}" style="background:${c}" title="${c}"></button>`).join('') +
      '<label class="sw sw-custom" title="Custom color"><input type="color"></label>';
    const input = el.querySelector('input');
    el.addEventListener('click', (e) => {
      const b = e.target.closest('.sw[data-c]');
      if (b) setProp(key, b.dataset.c, true);
    });
    input.addEventListener('input', () => setProp(key, input.value.toUpperCase(), false));
    input.addEventListener('change', () => setProp(key, input.value.toUpperCase(), true));
  }

  function syncSwatches(key, value) {
    const el = $(SWATCHES[key][0]), v = String(value).toLowerCase();
    let matched = false;
    el.querySelectorAll('.sw[data-c]').forEach((s) => {
      const on = s.dataset.c.toLowerCase() === v;
      matched = matched || on;
      s.classList.toggle('on', on);
    });
    el.querySelector('.sw-custom').classList.toggle('on', !matched);
    if (v[0] === '#') el.querySelector('input').value = v;
  }

  function syncProps() {
    const it = sel(), t = target(), type = it && it.type;
    $('#propsTitle').textContent = it ? TYPES[type].name : 'New shape style';
    $('#propsSub').textContent = it ? 'Selected shape' : 'Applies to the next shape you draw';
    const lines = !it || LINE_TYPES.includes(type), hasText = !it || TYPES[type].text;
    show('#fText', it && TYPES[type].text);
    show('#fLw', lines);
    show('#fChecks', lines);
    show('#fDash', lines);
    show('#fFill', it && ['rect', 'ellipse'].includes(type));
    show('#fRad', type !== 'marker');
    show('#fActions', !!it);
    const tabBtn = (name) => document.querySelector(`#tabs [data-tab="${name}"]`);
    tabBtn('label').classList.toggle('hidden', !hasText);
    const shown = activeTab === 'label' && !hasText ? 'shape' : activeTab;
    document.querySelectorAll('#tabs [data-tab]').forEach((b) => {
      b.classList.toggle('on', b.dataset.tab === shown);
      b.setAttribute('aria-selected', b.dataset.tab === shown);
    });
    document.querySelectorAll('.tabpane').forEach((p) => p.classList.toggle('hidden', p.dataset.pane !== shown));
    $('#borderNote').textContent = !it ? 'Outlines lines, arrowheads and labels.'
      : !LINE_TYPES.includes(type) ? 'Outlines the label. Without a background it outlines the letters.'
      : hasText ? 'Outlines the lines and arrowheads as well as the label.' : 'Outlines the lines and arrowheads.';
    if (it && TYPES[type].text) {
      propText.value = it.text;
      propText.placeholder = type === 'angle' ? `${angleInfo(it).deg}° (auto)` : PLACEHOLDER[type];
    }
    propLw.value = t.lw;
    propDash.checked = !!t.dash;
    propFill.checked = !!t.fill;
    for (const [k, id] of Object.entries(RANGES)) $(id).value = t[k];
    for (const [k, [id, fmt]] of Object.entries(OUTPUTS)) $(id).textContent = fmt(t[k]);
    for (const k in SWATCHES) syncSwatches(k, t[k]);
  }

  function setProp(key, value, done) {
    target()[key] = value;
    if (key === 'color') defaults.color = value;
    if (OUTPUTS[key]) $(OUTPUTS[key][0]).textContent = OUTPUTS[key][1](value);
    render();
    if (done) { syncProps(); if (sel()) commit(); }
  }

  propLw.addEventListener('input', () => setProp('lw', +propLw.value, false));
  propLw.addEventListener('change', () => setProp('lw', +propLw.value, true));
  for (const [k, id] of Object.entries(RANGES)) {
    const el = $(id);
    el.addEventListener('input', () => setProp(k, +el.value, false));
    el.addEventListener('change', () => setProp(k, +el.value, true));
  }
  propDash.addEventListener('change', () => setProp('dash', propDash.checked, true));
  propFill.addEventListener('change', () => setProp('fill', propFill.checked, true));
  propText.addEventListener('input', () => { const it = sel(); if (it) { it.text = propText.value; render(); } });
  propText.addEventListener('change', () => { if (sel()) commit(); });

  $('#btnDup').addEventListener('click', duplicateSelected);
  $('#btnFront').addEventListener('click', bringToFront);
  $('#btnDel').addEventListener('click', deleteSelected);
  $('#btnClear').addEventListener('click', () => {
    if (!doc.items.length || !confirm('Remove all annotations from this image?')) return;
    doc.items = []; selId = null;
    render(); syncProps(); commit();
  });

  // ---------- export ----------
  const loadImg = (src) => new Promise((res, rej) => { const i = new Image(); i.onload = () => res(i); i.onerror = rej; i.src = src; });
  const MIME = { png: 'image/png', jpeg: 'image/jpeg', webp: 'image/webp' };
  const EXT = { png: 'png', jpeg: 'jpg', webp: 'webp' };

  async function renderImage({ fmt = 'png', scale = 1, q = 0.92 } = {}) {
    const W = Math.max(1, Math.round(doc.w * scale)), H = Math.max(1, Math.round(doc.h * scale));
    const c = document.createElement('canvas');
    c.width = W; c.height = H;
    const ctx = c.getContext('2d');
    ctx.imageSmoothingQuality = 'high';
    ctx.drawImage(await loadImg(doc.image), 0, 0, W, H);
    const markup = itemsMarkup(true);
    render();
    // the overlay is rasterized at the output size so annotations stay crisp when scaling up
    const s = `<svg xmlns="http://www.w3.org/2000/svg" width="${W}" height="${H}" viewBox="0 0 ${doc.w} ${doc.h}">` +
      `<g font-family="${FONT}" font-weight="600">${markup}</g></svg>`;
    const overlay = await loadImg('data:image/svg+xml;charset=utf-8,' + encodeURIComponent(s));
    ctx.drawImage(overlay, 0, 0, W, H);
    return new Promise((res) => c.toBlob(res, MIME[fmt], q));
  }

  function download(blob, name) {
    const a = document.createElement('a');
    a.href = URL.createObjectURL(blob);
    a.download = name;
    document.body.appendChild(a);
    a.click();
    a.remove();
    setTimeout(() => URL.revokeObjectURL(a.href), 2000);
  }

  // Opens the system "Save as" window where supported. Must be called straight from a
  // click/keypress, so the blob is produced only after the location has been chosen.
  async function saveAs(getBlob, name, mime, ext, description) {
    if (window.showSaveFilePicker) {
      let handle = null;
      try {
        handle = await window.showSaveFilePicker({ suggestedName: name, types: [{ description, accept: { [mime]: [`.${ext}`] } }] });
      } catch (err) {
        if (err.name === 'AbortError') return false;
      }
      if (handle) {
        const w = await handle.createWritable();
        await w.write(await getBlob());
        await w.close();
        return true;
      }
    }
    download(await getBlob(), name);
    return true;
  }

  const fmtBytes = (n) => (n > 1048576 ? `${(n / 1048576).toFixed(1)} MB` : `${Math.max(1, Math.round(n / 1024))} KB`);
  const cleanName = (s, fallback) => (s.trim().replace(/\.(png|jpe?g|webp|json)$/i, '').replace(/[\\/:*?"<>|]+/g, '-') || fallback);
  const projectBlob = () => new Blob([JSON.stringify({ app: 'sizeshot', version: 2, ...doc })], { type: 'application/json' });

  const dlg = $('#saveDlg'), dlgName = $('#dlgName'), dlgPreview = $('#dlgPreview'), dlgInfo = $('#dlgInfo');
  const exp = { fmt: 'png', scale: 1, q: 0.92 };
  let dlgMode = 'image', expBlob = null, expToken = 0, previewTimer = null;
  const names = { image: 'sizeshot', project: 'sizeshot-project' };

  function openDialog(mode) {
    if (!doc.image) return;
    if (editing) finishEdit(true);
    dlgMode = mode;
    const img = mode === 'image';
    $('#dlgTitle').textContent = img ? 'Export image' : 'Save project';
    $('#dlgGo').textContent = img ? 'Save image…' : 'Save project…';
    dlg.querySelector('.dlg-body').classList.toggle('no-preview', !img);
    for (const id of ['#dlgPreviewWrap', '#dlgFmtRow', '#dlgScaleRow']) show(id, img);
    dlgName.value = names[mode];
    syncDialog();
    if (img) refreshPreview();
    else dlgInfo.textContent = `Contains the photo and all annotations (${fmtBytes(projectBlob().size)}). Load it later with Open to keep editing.`;
    dlg.showModal();
    dlgName.select();
  }

  function syncDialog() {
    $('#dlgExt').textContent = dlgMode === 'image' ? `.${EXT[exp.fmt]}` : '.json';
    show('#dlgQRow', dlgMode === 'image' && exp.fmt !== 'png');
    $('#dlgQ').value = exp.q;
    $('#dlgQOut').textContent = `${Math.round(exp.q * 100)}%`;
    dlg.querySelectorAll('#dlgFmt button').forEach((b) => b.classList.toggle('on', b.dataset.v === exp.fmt));
    dlg.querySelectorAll('#dlgScale button').forEach((b) => b.classList.toggle('on', +b.dataset.v === exp.scale));
  }

  function refreshPreview() {
    const tok = ++expToken;
    expBlob = null;
    dlgInfo.textContent = 'Rendering…';
    clearTimeout(previewTimer);
    previewTimer = setTimeout(async () => {
      const blob = await renderImage(exp);
      if (tok !== expToken) return;
      expBlob = blob;
      if (dlgPreview.src) URL.revokeObjectURL(dlgPreview.src);
      dlgPreview.src = URL.createObjectURL(blob);
      dlgInfo.textContent = `${Math.round(doc.w * exp.scale)} × ${Math.round(doc.h * exp.scale)} px · ${fmtBytes(blob.size)}`;
    }, 120);
  }

  $('#dlgFmt').addEventListener('click', (e) => {
    const b = e.target.closest('button');
    if (b) { exp.fmt = b.dataset.v; syncDialog(); refreshPreview(); }
  });
  $('#dlgScale').addEventListener('click', (e) => {
    const b = e.target.closest('button');
    if (b) { exp.scale = +b.dataset.v; syncDialog(); refreshPreview(); }
  });
  $('#dlgQ').addEventListener('input', () => { exp.q = +$('#dlgQ').value; syncDialog(); refreshPreview(); });
  dlgName.addEventListener('input', () => { names[dlgMode] = dlgName.value; });

  $('#dlgGo').addEventListener('click', async (e) => {
    e.preventDefault();
    const img = dlgMode === 'image';
    const ext = img ? EXT[exp.fmt] : 'json';
    const name = `${cleanName(dlgName.value, names[dlgMode] || 'sizeshot')}.${ext}`;
    const opts = { ...exp };
    try {
      const ok = img
        ? await saveAs(() => expBlob || renderImage(opts), name, MIME[opts.fmt], ext, 'Image')
        : await saveAs(async () => projectBlob(), name, 'application/json', ext, 'SizeShot project');
      if (!ok) return;
      dlg.close();
      toast(img ? 'Image saved' : 'Project saved');
    } catch (err) {
      console.error(err);
      toast('Saving failed.');
    }
  });

  $('#btnExport').addEventListener('click', () => openDialog('image'));
  $('#btnCopy').addEventListener('click', async () => {
    if (editing) finishEdit(true);
    try {
      await navigator.clipboard.write([new ClipboardItem({ 'image/png': renderImage() })]);
      toast('Image copied to clipboard');
    } catch (err) {
      console.error(err);
      toast('Copy is not supported here. Use Export instead.');
    }
  });

  // Save goes straight to the system "Save as" window; browsers without one get the dialog.
  async function saveProject() {
    if (!doc.image) return;
    if (editing) finishEdit(true);
    if (!window.showSaveFilePicker) { openDialog('project'); return; }
    try {
      if (await saveAs(async () => projectBlob(), 'sizeshot-project.json', 'application/json', 'json', 'SizeShot project')) toast('Project saved');
    } catch (err) {
      console.error(err);
      toast('Saving failed.');
    }
  }
  $('#btnSave').addEventListener('click', saveProject);

  // ---------- file inputs, drag & drop, paste ----------
  const fileImg = $('#fileImg'), fileProj = $('#fileProj');
  const pickImage = () => fileImg.click();
  $('#btnUpload').addEventListener('click', pickImage);
  $('#btnUpload2').addEventListener('click', pickImage);
  $('#btnOpen').addEventListener('click', () => fileProj.click());
  fileImg.addEventListener('change', () => { loadFile(fileImg.files[0]); fileImg.value = ''; });
  fileProj.addEventListener('change', () => { loadFile(fileProj.files[0]); fileProj.value = ''; });
  $('#btnUndo').addEventListener('click', undo);
  $('#btnRedo').addEventListener('click', redo);

  const dropmask = $('#dropmask');
  let dragDepth = 0;
  window.addEventListener('dragenter', (e) => { if (e.dataTransfer.types.includes('Files')) { dragDepth++; dropmask.classList.add('show'); } });
  window.addEventListener('dragleave', () => { if (--dragDepth <= 0) { dragDepth = 0; dropmask.classList.remove('show'); } });
  window.addEventListener('dragover', (e) => e.preventDefault());
  window.addEventListener('drop', (e) => {
    e.preventDefault();
    dragDepth = 0;
    dropmask.classList.remove('show');
    loadFile(e.dataTransfer.files[0]);
  });
  window.addEventListener('paste', (e) => {
    if (editing || /INPUT|TEXTAREA/.test(document.activeElement.tagName)) return;
    const file = [...(e.clipboardData?.files || [])].find((x) => x.type.startsWith('image/'));
    if (file) { e.preventDefault(); loadFile(file); }
  });

  // ---------- zoom buttons ----------
  $('#zIn').addEventListener('click', () => zoomAt(viewCenter(), 1.25));
  $('#zOut').addEventListener('click', () => zoomAt(viewCenter(), 0.8));
  $('#zFit').addEventListener('click', fit);
  $('#zVal').addEventListener('click', () => zoomAt(viewCenter(), pu));

  // drop focus from buttons after mouse clicks so Space/Enter keep working on the canvas
  document.addEventListener('click', (e) => {
    const b = e.target.closest('button');
    if (b && e.detail > 0) b.blur();
  });

  // ---------- keyboard ----------
  const TOOL_KEYS = { v: 'select', d: 'dim', c: 'callout', t: 'text', a: 'arrow', g: 'angle', r: 'rect', e: 'ellipse', m: 'marker' };

  window.addEventListener('keydown', (e) => {
    if (dlg.open || /INPUT|TEXTAREA|SELECT/.test(e.target.tagName)) return;
    const k = e.key.toLowerCase(), mod = e.ctrlKey || e.metaKey;
    if (mod && k === 'z') { e.preventDefault(); e.shiftKey ? redo() : undo(); return; }
    if (mod && k === 'y') { e.preventDefault(); redo(); return; }
    if (mod && k === 'd') { e.preventDefault(); duplicateSelected(); return; }
    if (mod && k === 's') { e.preventDefault(); saveProject(); return; }
    if (mod || e.altKey || !doc.image) return;
    if (k === ' ') { e.preventDefault(); spaceDown = true; wrap.classList.add('panning'); return; }
    if (k === 'escape') {
      if (creating) cancelCreate();
      else if (tool !== 'select') setTool('select');
      else if (selId) { selId = null; render(); syncProps(); }
      return;
    }
    if (k === 'delete' || k === 'backspace') { e.preventDefault(); deleteSelected(); return; }
    if (k === 'enter') { const it = sel(); if (it) { e.preventDefault(); startEdit(it, false); } return; }
    const arrows = { arrowleft: [-1, 0], arrowright: [1, 0], arrowup: [0, -1], arrowdown: [0, 1] };
    if (arrows[k] && sel()) {
      e.preventDefault();
      const step = (e.shiftKey ? 10 : 1) * pu, it = sel();
      it.pts = it.pts.map((p) => ({ x: p.x + arrows[k][0] * step, y: p.y + arrows[k][1] * step }));
      render(); commit();
      return;
    }
    if (k === '+' || k === '=') { zoomAt(viewCenter(), 1.25); return; }
    if (k === '-') { zoomAt(viewCenter(), 0.8); return; }
    if (k === '0') { fit(); return; }
    if (TOOL_KEYS[k]) setTool(TOOL_KEYS[k]);
  });
  window.addEventListener('keyup', (e) => {
    if (e.key === ' ') { spaceDown = false; if (!drag || drag.mode !== 'pan') wrap.classList.remove('panning'); }
  });

  // ---------- toast ----------
  let toastTimer = null;
  function toast(msg) {
    const t = $('#toast');
    t.textContent = msg;
    t.classList.add('show');
    clearTimeout(toastTimer);
    toastTimer = setTimeout(() => t.classList.remove('show'), 2400);
  }

  // ---------- boot ----------
  setTool('select');
  syncProps();
  updButtons();
  appEl.classList.add('no-image');
  try {
    const saved = JSON.parse(localStorage.getItem(STORE) || 'null');
    if (saved && saved.image && Array.isArray(saved.items)) setImage(saved.image, saved.items);
  } catch (err) { /* nothing to restore */ }
})();
