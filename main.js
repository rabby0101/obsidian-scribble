'use strict';
/*
 * Scribble (Rabby) - fast handwriting for Obsidian: full pages and sections inside notes.
 *
 * Why it stays fast however much is on the page:
 *  - Finished ink is baked into bitmap tiles once. Writing stroke 500 costs the same as stroke 1.
 *  - Only the stroke under the pen is drawn live, incrementally, on a small overlay canvas.
 *  - Tiles exist only near the visible area; scrolling is native.
 *  - The file is written a moment after the pen lifts, never during a stroke.
 *
 * One engine (Surface) drives both the full-page view and the sections embedded in notes.
 */
const { Plugin, PluginSettingTab, Setting, TextFileView, MarkdownRenderChild, FuzzySuggestModal, TFile, Notice, setIcon, normalizePath } = require('obsidian');

const VIEW_TYPE = 'rabby-scribble';
const EXT = 'scribble';
const FOLDER = 'Scribble';
const PAGE_W = 1000;     // logical page width; ink is stored in these units
const BAND_H = 500;      // logical height of one tile
const MAX_CSS_W = 1100;  // widest the page is drawn on screen
const LINE_GAP = 44;     // ruled-line spacing, logical units
const ERASER_R = 14;
const SPARE_LINES = 2;    // empty ruled lines kept under the ink of a section
const PALM_MS = 400;      // how long after the pen was last seen that other touches still count as the palm
// 'ink' follows the theme (dark on light, light on dark); every other colour is fixed.
const PALETTE = ['ink', '#8b8d98', '#e5484d', '#f76b15', '#ffb224', '#f5d90a', '#2f9e44', '#12a594',
  '#05a2c2', '#3b82f6', '#5b5bd6', '#8e4ec6', '#e93d82', '#a18072', '#111111', '#ffffff'];
const QUICK = ['ink', '#e5484d', '#3b82f6', '#2f9e44'];   // the four colours kept on the toolbar; a newly picked colour takes the first place
const WIDTHS = [1.2, 1.8, 2.8, 4.6, 8];                  // one-tap widths; the slider gives anything between MIN_W and MAX_W
const MIN_W = 0.6, MAX_W = 14;
const PREFS_KEY = 'rabby-scribble-pen';
const BACKGROUNDS = { ruled: 'Ruled lines', grid: 'Grid', dots: 'Dots', none: 'Blank' };
const ERASERS = { partial: 'Partial: erase only what it touches', stroke: 'Whole stroke: erase each stroke it touches' };
const DEFAULT_SETTINGS = { background: 'ruled', eraser: 'partial', eraserSize: ERASER_R, shapes: true, shapeHold: 500 };
const SHAPE_STILL_PX = 4;   // the pen counts as held still while it stays within this many screen pixels
// Pen types: name, toolbar icon, starting size and colour. How each one LOOKS is in LOOKS below.
const PENS = {
  fountain: { label: 'Fountain pen', icon: 'pen-tool', def: { size: 3.2, color: 'ink' } },
  ball: { label: 'Ballpoint', icon: 'pen', def: { size: 2.2, color: 'ink' } },
  pencil: { label: 'Pencil', icon: 'pencil', def: { size: 1.6, color: 'ink' } },
  marker: { label: 'Highlighter', icon: 'highlighter', def: { size: 8, color: '#f5d90a' } },
};
// The look of each pen (Settings > Scribble > Pens). Strokes saved before pen types existed keep their original look.
//  width      how wide the pen draws at a given size (multiplier)
//  pressure   0 = pressing harder changes nothing, 1 = from hairline (light) to double width (hard)
//  smoothing  0 = width follows the pen instantly, 0.95 = changes very gently
//  opacity    1 = solid; lower = see-through (overlaps inside one stroke never darken)
//  cap        line ends: 'round' or 'square'
//  under      drawn beneath all other ink (so highlighting never covers writing)
//  angle, hairline   fountain pen nib: angle of the broad edge in degrees, and the thinnest line as a share of the full width
const LOOK_DEFAULTS = {
  fountain: { width: 1.3, pressure: 0.8, smoothing: 0.45, opacity: 1, cap: 'round', under: false, angle: 25, hairline: 0.1 },
  ball: { width: 1.0, pressure: 0.2, smoothing: 0.65, opacity: 1, cap: 'round', under: false },
  pencil: { width: 0.9, pressure: 0.15, smoothing: 0.65, opacity: 0.75, cap: 'round', under: false },
  marker: { width: 2.0, pressure: 0, smoothing: 0, opacity: 0.35, cap: 'square', under: true },
};
const LOOK_LIMITS = { width: [0.3, 3], pressure: [0, 1], smoothing: [0, 0.95], opacity: [0.1, 1], angle: [-90, 90], hairline: [0, 1] };
function makeLooks(saved) {   // defaults + the user's changes, each value checked
  const out = {};
  for (const k in LOOK_DEFAULTS) {
    const L = out[k] = Object.assign({}, LOOK_DEFAULTS[k]), v = (saved && saved[k]) || {};
    for (const f in L) {
      if (LOOK_LIMITS[f]) { if (typeof v[f] === 'number' && isFinite(v[f])) L[f] = Math.min(LOOK_LIMITS[f][1], Math.max(LOOK_LIMITS[f][0], v[f])); }
      else if (f === 'cap') { if (v.cap === 'round' || v.cap === 'square') L.cap = v.cap; }
      else if (f === 'under') { if (typeof v.under === 'boolean') L.under = v.under; }
    }
  }
  return out;
}
let LOOKS = makeLooks(null);
const isUnder = s => !!(LOOKS[s.t] && LOOKS[s.t].under);
const lookAlpha = k => (LOOKS[k] && LOOKS[k].opacity < 1) ? LOOKS[k].opacity : '';
const cssColor = c => c === 'ink' ? 'var(--text-normal)' : c;

/* ---------- ink geometry: one routine for both live drawing and re-rendering ---------- */

function penWidth(st, pr, dx, dy) {
  const L = LOOKS[st.kind];
  if (!L) return st.size * (0.4 + 1.2 * pr);                                  // strokes from before pen types
  let w = st.size * L.width * Math.max(0.08, 1 + L.pressure * (2 * pr - 1));  // average pressure (0.5) = the set width
  if (L.angle !== undefined) {   // broad nib: full width across the nib edge, down to the hairline along it
    const a = L.angle * Math.PI / 180, l = Math.hypot(dx, dy);
    const nib = l ? Math.abs(dx * Math.sin(a) + dy * Math.cos(a)) / l : 0.6;
    w *= L.hairline + (1 - L.hairline) * nib * Math.sqrt(nib);
  }
  return w;
}
function maxHalf(s) {   // widest a stroke can get, from either side of its centre line
  const L = LOOKS[s.t];
  return L ? s.s * L.width * (1 + L.pressure) / 2 + 0.5 : s.s * 0.8 + 0.5;
}

function inkBegin(ctx, st, x, y, pr) {
  st.n = 1; st.px = x; st.py = y; st.w = penWidth(st, pr, 0, 0);
  ctx.beginPath(); ctx.arc(x, y, st.w / 2, 0, 6.2832); ctx.fill();
}
function inkMove(ctx, st, x, y, pr) {
  const mx = (st.px + x) / 2, my = (st.py + y) / 2;
  const w = penWidth(st, pr, x - st.px, y - st.py), L = LOOKS[st.kind], k = L ? L.smoothing : 0.65;
  st.w = st.w * k + w * (1 - k);
  ctx.lineWidth = st.w;
  ctx.beginPath();
  if (st.n === 1) { ctx.moveTo(st.px, st.py); ctx.lineTo(mx, my); }
  else { ctx.moveTo(st.mx, st.my); ctx.quadraticCurveTo(st.px, st.py, mx, my); }
  ctx.stroke();
  st.mx = mx; st.my = my; st.px = x; st.py = y; st.n++;
}
function inkEnd(ctx, st) {
  if (st.n < 2) return;
  ctx.lineWidth = st.w;
  ctx.beginPath(); ctx.moveTo(st.mx, st.my); ctx.lineTo(st.px, st.py); ctx.stroke();
}
function drawStroke(ctx, s) {
  const p = s.p, st = { size: s.s, kind: s.t };
  const L = LOOKS[s.t];
  ctx.lineCap = L ? L.cap : 'round'; ctx.lineJoin = 'round';
  inkBegin(ctx, st, p[0], p[1], p[2]);
  for (let i = 3; i < p.length; i += 3) inkMove(ctx, st, p[i], p[i + 1], p[i + 2]);
  inkEnd(ctx, st);
}
let scratch = null;   // reused for see-through pens: the stroke is drawn solid here, then laid on the page see-through
function paintStroke(ctx, s, color) {
  if (s.p.length < 3) return;
  ctx.strokeStyle = color; ctx.fillStyle = color;
  const L = LOOKS[s.t];
  if (L && L.opacity < 1) {
    const m = typeof ctx.getTransform === 'function' ? ctx.getTransform() : null;
    const cv = ctx.canvas;
    if (m && typeof m.a === 'number' && cv && cv.width && typeof document !== 'undefined' && document.createElement) {
      const b = s.bb;
      const x0 = Math.max(0, Math.floor(b[0] * m.a + m.e)), y0 = Math.max(0, Math.floor(b[1] * m.d + m.f));
      const x1 = Math.min(cv.width, Math.ceil(b[2] * m.a + m.e)), y1 = Math.min(cv.height, Math.ceil(b[3] * m.d + m.f));
      if (x1 <= x0 || y1 <= y0) return;
      const w = x1 - x0, h = y1 - y0;
      if (!scratch) scratch = document.createElement('canvas');
      if (scratch.width < w || scratch.height < h) { scratch.width = Math.max(scratch.width, w); scratch.height = Math.max(scratch.height, h); }
      const sc = scratch.getContext('2d');
      sc.setTransform(1, 0, 0, 1, 0, 0); sc.clearRect(0, 0, w, h);
      sc.setTransform(m.a, 0, 0, m.d, m.e - x0, m.f - y0);
      sc.strokeStyle = color; sc.fillStyle = color;
      drawStroke(sc, s);
      ctx.save(); ctx.setTransform(1, 0, 0, 1, 0, 0); ctx.globalAlpha = L.opacity;
      ctx.drawImage(scratch, 0, 0, w, h, x0, y0, w, h);
      ctx.restore();
      return;
    }
    ctx.globalAlpha = L.opacity;   // fallback without a scratch canvas
    drawStroke(ctx, s);
    ctx.globalAlpha = 1;
    return;
  }
  drawStroke(ctx, s);
}
function computeBB(s) {
  const p = s.p;
  let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
  for (let i = 0; i < p.length; i += 3) {
    if (p[i] < x0) x0 = p[i]; if (p[i] > x1) x1 = p[i];
    if (p[i + 1] < y0) y0 = p[i + 1]; if (p[i + 1] > y1) y1 = p[i + 1];
  }
  const pad = maxHalf(s) + 1;
  s.bb = [x0 - pad, y0 - pad, x1 + pad, y1 + pad];
}
// Partial erase: returns the pieces of stroke s left outside the circle (x, y, r), or null if the circle misses its ink.
// Segments near the circle are first divided finely, so the cut follows the eraser edge.
function cutStroke(s, x, y, r) {
  const L = LOOKS[s.t], half = L ? s.s * L.width / 2 : s.s * 0.8;
  const R = r + half * 0.6, R2 = R * R, step = Math.max(0.6, R / 3), p = s.p, q = [];
  for (let i = 0; i < p.length; i += 3) {
    if (i) {
      const ax = p[i - 3], ay = p[i - 2], bx = p[i], by = p[i + 1], len = Math.hypot(bx - ax, by - ay);
      if (len > step && distSegSq(x, y, ax, ay, bx, by) <= (R + step) * (R + step)) {
        const n = Math.ceil(len / step);
        for (let j = 1; j < n; j++) {
          const t = j / n;
          q.push(Math.round((ax + (bx - ax) * t) * 10) / 10, Math.round((ay + (by - ay) * t) * 10) / 10, Math.round((p[i - 1] + (p[i + 2] - p[i - 1]) * t) * 100) / 100);
        }
      }
    }
    q.push(p[i], p[i + 1], p[i + 2]);
  }
  const pieces = []; let run = [], cut = false;
  for (let i = 0; i < q.length; i += 3) {
    const dx = q[i] - x, dy = q[i + 1] - y;
    if (dx * dx + dy * dy <= R2) { cut = true; if (run.length) { pieces.push(run); run = []; } }
    else run.push(q[i], q[i + 1], q[i + 2]);
  }
  if (!cut) return null;
  if (run.length) pieces.push(run);
  const out = [];
  for (const pp of pieces) {
    if (pp.length < 6) continue;   // a single leftover point would show as a stray dot
    const n = { c: s.c, s: s.s, p: pp }; if (s.t) n.t = s.t;
    computeBB(n); out.push(n);
  }
  return out;
}
function distSegSq(x, y, ax, ay, bx, by) {
  const dx = bx - ax, dy = by - ay, l = dx * dx + dy * dy;
  let t = l ? ((x - ax) * dx + (y - ay) * dy) / l : 0;
  t = t < 0 ? 0 : t > 1 ? 1 : t;
  const cx = ax + t * dx - x, cy = ay + t * dy - y;
  return cx * cx + cy * cy;
}
function hits(s, x, y, r) {
  const b = s.bb;
  if (x < b[0] - r || x > b[2] + r || y < b[1] - r || y > b[3] + r) return false;
  const p = s.p, rr = (r + maxHalf(s)) * (r + maxHalf(s));
  if (p.length === 3) return distSegSq(x, y, p[0], p[1], p[0], p[1]) <= rr;
  for (let i = 3; i < p.length; i += 3) {
    if (distSegSq(x, y, p[i - 3], p[i - 2], p[i], p[i + 1]) <= rr) return true;
  }
  return false;
}
function inPoly(x, y, q) {   // q = [x0, y0, x1, y1, ...], ray casting
  let inside = false;
  for (let i = 0, j = q.length - 2; i < q.length; j = i, i += 2) {
    const xi = q[i], yi = q[i + 1], xj = q[j], yj = q[j + 1];
    if ((yi > y) !== (yj > y) && x < (xj - xi) * (y - yi) / (yj - yi) + xi) inside = !inside;
  }
  return inside;
}
function unionBB(list) {
  const b = [Infinity, Infinity, -Infinity, -Infinity];
  for (const s of list) { b[0] = Math.min(b[0], s.bb[0]); b[1] = Math.min(b[1], s.bb[1]); b[2] = Math.max(b[2], s.bb[2]); b[3] = Math.max(b[3], s.bb[3]); }
  return b;
}
function shifted(s, dx, dy) {   // a moved copy of a stroke
  const p = s.p.slice();
  for (let i = 0; i < p.length; i += 3) { p[i] = Math.round((p[i] + dx) * 10) / 10; p[i + 1] = Math.round((p[i + 1] + dy) * 10) / 10; }
  const n = { c: s.c, s: s.s, p }; if (s.t) n.t = s.t;
  computeBB(n); return n;
}
function parseDoc(data) {
  const out = [];
  if (!data || !data.trim()) return out;
  let doc;
  try { doc = JSON.parse(data); } catch (e) { console.error('Scribble: could not read file', e); return null; }
  for (const r of (doc && doc.strokes) || []) {
    if (!r || !Array.isArray(r.p) || r.p.length < 3) continue;
    const s = { c: r.c || 'ink', s: +r.s || 2.8, p: r.p };
    if (PENS[r.t]) s.t = r.t;
    computeBB(s);
    out.push(s);
  }
  return out;
}

/* ---------- shape recognition: draw, hold still, and the stroke snaps to a clean shape ---------- */
// Input: flat [x, y, x, y, ...] of the hand-drawn stroke (page units).
// Output: null (leave the stroke alone) or { kind, xy: flat clean points, ax, ay (anchor for hold-to-adjust) }.

function pathLen(q) { let L = 0; for (let i = 2; i < q.length; i += 2) L += Math.hypot(q[i] - q[i - 2], q[i + 1] - q[i - 1]); return L; }
function resample(q, step) {   // evenly spaced points along a polyline
  const out = [q[0], q[1]]; let carry = 0;
  for (let i = 2; i < q.length; i += 2) {
    let ax = q[i - 2], ay = q[i - 1]; const bx = q[i], by = q[i + 1];
    let seg = Math.hypot(bx - ax, by - ay);
    while (carry + seg >= step) {
      const t = (step - carry) / seg;
      ax += (bx - ax) * t; ay += (by - ay) * t; seg = Math.hypot(bx - ax, by - ay);
      out.push(ax, ay); carry = 0;
    }
    carry += seg;
  }
  if (out[out.length - 2] !== q[q.length - 2] || out[out.length - 1] !== q[q.length - 1]) out.push(q[q.length - 2], q[q.length - 1]);
  return out;
}
function rdp(q, i0, i1, eps, keep) {   // Ramer-Douglas-Peucker on point indices
  let best = -1, dmax = 0;
  for (let i = i0 + 1; i < i1; i++) {
    const d = Math.sqrt(distSegSq(q[2 * i], q[2 * i + 1], q[2 * i0], q[2 * i0 + 1], q[2 * i1], q[2 * i1 + 1]));
    if (d > dmax) { dmax = d; best = i; }
  }
  if (dmax > eps) { rdp(q, i0, best, eps, keep); keep.push(best); rdp(q, best, i1, eps, keep); }
}
function angleAt(ax, ay, bx, by, cx, cy) {   // interior angle at b, degrees
  const ux = ax - bx, uy = ay - by, vx = cx - bx, vy = cy - by;
  const c = (ux * vx + uy * vy) / (Math.hypot(ux, uy) * Math.hypot(vx, vy) || 1);
  return Math.acos(Math.max(-1, Math.min(1, c))) * 180 / Math.PI;
}
function snapAngle(a, step, tol) {   // radians; snap to multiples of step (radians) within tol
  const k = Math.round(a / step), d = a - k * step;
  return Math.abs(d) <= tol ? k * step : a;
}
function polyPoints(v, closed, step) {   // vertices [[x,y],...] -> dense flat points
  const q = [];
  const n = v.length, m = closed ? n : n - 1;
  for (let i = 0; i < m; i++) {
    const [ax, ay] = v[i], [bx, by] = v[(i + 1) % n];
    const k = Math.max(1, Math.ceil(Math.hypot(bx - ax, by - ay) / step));
    for (let j = 0; j < k; j++) q.push(ax + (bx - ax) * j / k, ay + (by - ay) * j / k);
  }
  if (closed) { q.push(v[0][0], v[0][1]); const [bx, by] = v[1 % n], dx = bx - v[0][0], dy = by - v[0][1], l = Math.hypot(dx, dy) || 1; q.push(v[0][0] + dx / l * Math.min(step, l), v[0][1] + dy / l * Math.min(step, l)); }   // overlap a hair so the join closes
  else q.push(v[n - 1][0], v[n - 1][1]);
  return q;
}
function ellipsePoints(cx, cy, a, b, th, step) {
  const per = Math.PI * (3 * (a + b) - Math.sqrt((3 * a + b) * (a + 3 * b)));
  const n = Math.max(40, Math.ceil(per / step)), c = Math.cos(th), s = Math.sin(th), q = [];
  for (let i = 0; i <= n + 1; i++) {   // one step past the start so the join closes
    const t = 2 * Math.PI * i / n, u = a * Math.cos(t), w = b * Math.sin(t);
    q.push(cx + u * c - w * s, cy + u * s + w * c);
  }
  return q;
}
function fitCircle(q) {   // algebraic (Kasa) least squares
  let sx = 0, sy = 0, n = q.length / 2;
  for (let i = 0; i < q.length; i += 2) { sx += q[i]; sy += q[i + 1]; }
  const mx = sx / n, my = sy / n;
  let suu = 0, svv = 0, suv = 0, suuu = 0, svvv = 0, suvv = 0, svuu = 0;
  for (let i = 0; i < q.length; i += 2) {
    const u = q[i] - mx, v = q[i + 1] - my;
    suu += u * u; svv += v * v; suv += u * v; suuu += u * u * u; svvv += v * v * v; suvv += u * v * v; svuu += v * u * u;
  }
  const det = suu * svv - suv * suv; if (Math.abs(det) < 1e-9) return null;
  const r1 = (suuu + suvv) / 2, r2 = (svvv + svuu) / 2;
  const uc = (r1 * svv - r2 * suv) / det, vc = (r2 * suu - r1 * suv) / det;
  const R = Math.sqrt(uc * uc + vc * vc + (suu + svv) / n);
  return { cx: uc + mx, cy: vc + my, r: R };
}

function recognizeShape(raw) {
  if (raw.length < 16) return null;
  let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
  for (let i = 0; i < raw.length; i += 2) { x0 = Math.min(x0, raw[i]); x1 = Math.max(x1, raw[i]); y0 = Math.min(y0, raw[i + 1]); y1 = Math.max(y1, raw[i + 1]); }
  const diag = Math.hypot(x1 - x0, y1 - y0);
  if (diag < 16) return null;                        // too small to be a deliberate shape
  const L = pathLen(raw);
  const q = resample(raw, Math.max(1, L / 160));      // ~160 even points, whatever the drawing speed
  const n = q.length / 2, step = 2;
  const sx = q[0], sy = q[1], ex = q[q.length - 2], ey = q[q.length - 1];
  const gap = Math.hypot(ex - sx, ey - sy);
  const closed = gap < Math.max(0.12 * L, 0.2 * diag) && L > 2.2 * diag * 0.9;

  if (!closed) {
    const chord = gap;
    // straight line: nothing strays far from the chord
    let dev = 0;
    for (let i = 0; i < q.length; i += 2) dev = Math.max(dev, Math.sqrt(distSegSq(q[i], q[i + 1], sx, sy, ex, ey)));
    if (chord > 0.85 * L || dev < 0.07 * chord) {
      if (L > 1.25 * chord) { /* went back on itself: maybe an arrow, below */ }
      else {
        let a = Math.atan2(ey - sy, ex - sx); a = snapAngle(a, Math.PI / 4, 6 * Math.PI / 180);
        const tx = sx + Math.cos(a) * chord, ty = sy + Math.sin(a) * chord;
        return { kind: 'line', xy: polyPoints([[sx, sy], [tx, ty]], false, step), ax: sx, ay: sy };
      }
    }
    // arrow: a straight shaft to the farthest point (the tip), then a short head that stays near the tip
    let ti = 0, td = 0;
    for (let i = 0; i < n; i++) { const d = Math.hypot(q[2 * i] - sx, q[2 * i + 1] - sy); if (d > td) { td = d; ti = i; } }
    for (let i = 0; i < ti; i++) { if (Math.hypot(q[2 * i] - sx, q[2 * i + 1] - sy) >= 0.96 * td) { ti = i; td = Math.hypot(q[2 * i] - sx, q[2 * i + 1] - sy); break; } }   // first arrival at the tip (the head may pass it again)
    if (ti > 4 && ti < n - 2) {
      const tx = q[2 * ti], ty = q[2 * ti + 1];
      let sdev = 0;
      for (let i = 0; i <= ti; i++) sdev = Math.max(sdev, Math.sqrt(distSegSq(q[2 * i], q[2 * i + 1], sx, sy, tx, ty)));
      let near = true, headLen = 0;
      for (let i = ti; i < n; i++) { if (Math.hypot(q[2 * i] - tx, q[2 * i + 1] - ty) > 0.45 * td) near = false; }
      for (let i = ti + 1; i < n; i++) headLen += Math.hypot(q[2 * i] - q[2 * i - 2], q[2 * i + 1] - q[2 * i - 1]);
      if (sdev < 0.08 * td && near && headLen > 0.12 * td && headLen < 1.4 * td) {
        let a = Math.atan2(ty - sy, tx - sx); a = snapAngle(a, Math.PI / 4, 6 * Math.PI / 180);
        const X = sx + Math.cos(a) * td, Y = sy + Math.sin(a) * td, h = Math.min(60, Math.max(10, 0.2 * td)), w = 28 * Math.PI / 180;
        const b1 = [X - h * Math.cos(a - w), Y - h * Math.sin(a - w)], b2 = [X - h * Math.cos(a + w), Y - h * Math.sin(a + w)];
        const xy = polyPoints([[sx, sy], [X, Y], b1], false, step);
        xy.push(...polyPoints([b1, [X, Y], b2], false, step).slice(2));
        return { kind: 'arrow', xy, ax: sx, ay: sy };
      }
    }
    // arc: points lie on a circle, and it doesn't go all the way round
    const c = fitCircle(q);
    if (c && c.r < 4 * diag) {
      let err = 0;
      for (let i = 0; i < q.length; i += 2) err += Math.abs(Math.hypot(q[i] - c.cx, q[i + 1] - c.cy) - c.r);
      err /= n;
      if (err < 0.035 * c.r + 0.6) {
        const a0 = Math.atan2(sy - c.cy, sx - c.cx);
        let sweep = 0, prev = a0;
        for (let i = 1; i < n; i++) { const a = Math.atan2(q[2 * i + 1] - c.cy, q[2 * i] - c.cx); let d = a - prev; if (d > Math.PI) d -= 2 * Math.PI; if (d < -Math.PI) d += 2 * Math.PI; sweep += d; prev = a; }
        if (Math.abs(sweep) > 0.35 && Math.abs(sweep) < 2 * Math.PI * 0.92) {
          const k = Math.max(16, Math.ceil(Math.abs(sweep) * c.r / step)), xy = [];
          for (let i = 0; i <= k; i++) { const a = a0 + sweep * i / k; xy.push(c.cx + c.r * Math.cos(a), c.cy + c.r * Math.sin(a)); }
          return { kind: 'arc', xy, ax: sx, ay: sy };
        }
      }
    }
    return null;
  }

  // ----- closed: ellipse/circle or polygon, whichever fits better -----
  let mx = 0, my = 0;
  for (let i = 0; i < q.length; i += 2) { mx += q[i]; my += q[i + 1]; }
  mx /= n; my /= n;
  let cxx = 0, cyy = 0, cxy = 0;
  for (let i = 0; i < q.length; i += 2) { const u = q[i] - mx, v = q[i + 1] - my; cxx += u * u; cyy += v * v; cxy += u * v; }
  cxx /= n; cyy /= n; cxy /= n;
  let th = 0.5 * Math.atan2(2 * cxy, cxx - cyy);
  const ct = Math.cos(th), st = Math.sin(th);
  let ua = 0, va = 0;   // extents along the principal axes
  for (let i = 0; i < q.length; i += 2) { const u = q[i] - mx, v = q[i + 1] - my; ua = Math.max(ua, Math.abs(u * ct + v * st)); va = Math.max(va, Math.abs(-u * st + v * ct)); }
  let ea = Math.sqrt(2 * (cxx * ct * ct + 2 * cxy * ct * st + cyy * st * st));
  let eb = Math.sqrt(2 * (cxx * st * st - 2 * cxy * ct * st + cyy * ct * ct));
  let eErr = 0;
  for (let i = 0; i < q.length; i += 2) {
    const u = q[i] - mx, v = q[i + 1] - my, pu = u * ct + v * st, pv = -u * st + v * ct;
    const r = Math.hypot(pu / ea, pv / eb);
    eErr += Math.abs(r - 1) * Math.hypot(pu, pv) / (r || 1);
  }
  eErr /= n;

  // polygon corners: RDP from the start point and from the point farthest from it
  let fi = 0, fd = 0;
  for (let i = 0; i < n; i++) { const d = Math.hypot(q[2 * i] - sx, q[2 * i + 1] - sy); if (d > fd) { fd = d; fi = i; } }
  const eps = 0.07 * diag, keep = [0];
  rdp(q, 0, fi, eps, keep); keep.push(fi); rdp(q, fi, n - 1, eps, keep);
  let v = keep.map(i => [q[2 * i], q[2 * i + 1]]);
  // merge corners that are close together, then drop corners that are nearly straight
  for (let changed = true; changed && v.length > 2;) {
    changed = false;
    for (let i = 0; i < v.length && v.length > 2; i++) {
      const a = v[(i - 1 + v.length) % v.length], b = v[i], c = v[(i + 1) % v.length];
      if (Math.hypot(b[0] - c[0], b[1] - c[1]) < 0.12 * diag) { v[i] = [(b[0] + c[0]) / 2, (b[1] + c[1]) / 2]; v.splice((i + 1) % v.length, 1); changed = true; break; }
      if (angleAt(a[0], a[1], b[0], b[1], c[0], c[1]) > 155) { v.splice(i, 1); changed = true; break; }
    }
  }
  // how sharp the corners are: share of the stroke's total turning that happens right at the corners.
  // A real polygon turns almost only at its corners; a wobbly circle turns everywhere.
  let conc = 0;
  if (v.length >= 3) {
    const k = 3, head = i => { const a = Math.max(0, Math.min(n - 1 - k, i)); return Math.atan2(q[2 * (a + k) + 1] - q[2 * a + 1], q[2 * (a + k)] - q[2 * a]); };
    const w = Math.max(3, Math.round(n / 30));
    for (const p of v) {
      let bi = 0, bd = Infinity;
      for (let i = 0; i < n; i++) { const d = Math.hypot(q[2 * i] - p[0], q[2 * i + 1] - p[1]); if (d < bd) { bd = d; bi = i; } }
      // heading just before the corner vs just after it (a corner at the very start/end compares end with start)
      const before = bi - w - k < 0 ? head(n - 1 - k - (w - bi)) : head(bi - w - k), after = bi + w > n - 1 - k ? head(bi + w - (n - 1 - k)) : head(bi + w);
      let d = after - before; while (d > Math.PI) d -= 2 * Math.PI; while (d < -Math.PI) d += 2 * Math.PI;
      conc += Math.abs(d);
    }
    conc /= 2 * Math.PI;
  }
  let pErr = Infinity;
  if (v.length >= 3 && v.length <= 8) {
    pErr = 0;
    for (let i = 0; i < q.length; i += 2) {
      let d = Infinity;
      for (let j = 0; j < v.length; j++) { const A = v[j], B = v[(j + 1) % v.length]; d = Math.min(d, distSegSq(q[i], q[i + 1], A[0], A[1], B[0], B[1])); }
      pErr += Math.sqrt(d);
    }
    pErr /= n;
  }
  const lim = 0.045 * diag;
  if (Math.min(eErr, pErr) > lim) return null;
  if (eErr > lim && !(pErr <= lim)) return null;

  // polygon only when it has real corners and fits better than an ellipse; a polygon has more freedom, so it must fit better
  const polygonish = pErr < eErr && (v.length <= 4 ? conc > 0.6 : conc > 0.85 && pErr < 0.8 * eErr);
  if (!polygonish) {
    if (ea / eb < 1.18) { const r = (ea + eb) / 2; return { kind: 'circle', xy: ellipsePoints(mx, my, r, r, 0, step), ax: mx, ay: my }; }
    th = snapAngle(th, Math.PI / 2, 8 * Math.PI / 180);
    return { kind: 'ellipse', xy: ellipsePoints(mx, my, ea, eb, th, step), ax: mx, ay: my };
  }

  let cx = 0, cy = 0; for (const p of v) { cx += p[0]; cy += p[1]; } cx /= v.length; cy /= v.length;
  if (v.length === 4) {
    const angs = v.map((b, i) => { const a = v[(i + 3) % 4], c = v[(i + 1) % 4]; return angleAt(a[0], a[1], b[0], b[1], c[0], c[1]); });
    if (angs.every(a => Math.abs(a - 90) < 20)) {
      // rectangle: average edge direction (mod 90°), extents of the corners along it
      let sc = 0, ss = 0;
      for (let i = 0; i < 4; i++) { const a = v[i], b = v[(i + 1) % 4], d = Math.atan2(b[1] - a[1], b[0] - a[0]) * 4; const l = Math.hypot(b[0] - a[0], b[1] - a[1]); sc += Math.cos(d) * l; ss += Math.sin(d) * l; }
      let o = Math.atan2(ss, sc) / 4; o = snapAngle(o, Math.PI / 2, 8 * Math.PI / 180);
      const co = Math.cos(o), so = Math.sin(o);
      let u0 = Infinity, u1 = -Infinity, w0 = Infinity, w1 = -Infinity;
      for (const p of v) { const u = (p[0] - cx) * co + (p[1] - cy) * so, w = -(p[0] - cx) * so + (p[1] - cy) * co; u0 = Math.min(u0, u); u1 = Math.max(u1, u); w0 = Math.min(w0, w); w1 = Math.max(w1, w); }
      let hu = (u1 - u0) / 2, hw = (w1 - w0) / 2, ou = (u0 + u1) / 2, ow = (w0 + w1) / 2;
      let kind = 'rectangle';
      if (Math.max(hu, hw) / Math.min(hu, hw) < 1.12) { hu = hw = (hu + hw) / 2; kind = 'square'; }
      const ccx = cx + ou * co - ow * so, ccy = cy + ou * so + ow * co;
      const corner = (a, b) => [ccx + a * co - b * so, ccy + a * so + b * co];
      const rv = [corner(-hu, -hw), corner(hu, -hw), corner(hu, hw), corner(-hu, hw)];
      return { kind, xy: polyPoints(rv, true, step), ax: ccx, ay: ccy };
    }
  }
  if (v.length === 3) {
    // right angle: if one corner is close to 90°, move it onto the circle over the opposite side
    for (let i = 0; i < 3; i++) {
      const a = v[(i + 2) % 3], b = v[i], c = v[(i + 1) % 3];
      if (Math.abs(angleAt(a[0], a[1], b[0], b[1], c[0], c[1]) - 90) < 10) {
        const mx2 = (a[0] + c[0]) / 2, my2 = (a[1] + c[1]) / 2, R = Math.hypot(a[0] - c[0], a[1] - c[1]) / 2;
        const d = Math.hypot(b[0] - mx2, b[1] - my2) || 1;
        v[i] = [mx2 + (b[0] - mx2) / d * R, my2 + (b[1] - my2) / d * R];
        break;
      }
    }
    return { kind: 'triangle', xy: polyPoints(v, true, step), ax: cx, ay: cy };
  }
  if (v.length >= 5) {
    // nearly regular (even sides): make it exactly regular
    const lens = v.map((p, i) => Math.hypot(v[(i + 1) % v.length][0] - p[0], v[(i + 1) % v.length][1] - p[1]));
    const avg = lens.reduce((s, x) => s + x, 0) / lens.length;
    if (lens.every(l => Math.abs(l - avg) < 0.3 * avg)) {
      const R = v.reduce((s, p) => s + Math.hypot(p[0] - cx, p[1] - cy), 0) / v.length;
      const a0 = Math.atan2(v[0][1] - cy, v[0][0] - cx), dir = ((v[1][0] - v[0][0]) * (cy - v[0][1]) - (v[1][1] - v[0][1]) * (cx - v[0][0])) > 0 ? -1 : 1;
      const rv = v.map((_, i) => { const a = a0 + dir * 2 * Math.PI * i / v.length; return [cx + R * Math.cos(a), cy + R * Math.sin(a)]; });
      return { kind: 'polygon', xy: polyPoints(rv, true, step), ax: cx, ay: cy };
    }
  }
  return { kind: v.length === 4 ? 'quadrilateral' : 'polygon', xy: polyPoints(v, true, step), ax: cx, ay: cy };
}

/* ---------- toolbar: docked on a full page; one floating copy shared by every section in notes ---------- */

class Bar {
  constructor(plugin, el, getSurface, floating) {
    this.plugin = plugin; this.el = el; this.getSurface = getSurface;
    const prefs = plugin.prefs;
    const btn = (title, fn, icon, text) => {
      const b = el.createDiv({ cls: 'scr-btn', attr: { 'aria-label': title } });
      if (icon) setIcon(b, icon); else if (text) b.setText(text);
      b.addEventListener('click', fn);
      return b;
    };
    const sep = () => el.createDiv({ cls: 'scr-sep' });
    const set = (k, v, pen) => {
      prefs[k] = v; if (pen) prefs.tool = 'pen';
      if (k === 'tool' || pen) for (const sf of plugin.surfaces) sf.clearSelection();
      plugin.savePrefs(); plugin.refreshBars();
    };
    const withSurface = f => () => { const s = getSurface(); if (s) f(s); };
    this.set = set;
    this.quick = [];
    if (!floating) { btn('Back', withSurface(s => { if (s.opts.onBack) s.opts.onBack(); }), 'arrow-left'); sep(); }
    this.pen = btn('Pen', () => { if (prefs.tool !== 'pen') set('tool', 'pen'); else this.togglePop('pen', this.pen); }, PENS[prefs.pen].icon);
    this.penIcon = prefs.pen;
    this.eraser = btn('Eraser', () => set('tool', 'eraser'), 'eraser');
    this.select = btn('Select: draw around ink to move, copy, recolour or delete it', () => set('tool', 'select'), 'lasso');
    sep();
    for (let i = 0; i < QUICK.length; i++) {
      const b = btn('Colour', () => this.pickColor(prefs.quick[i]));
      this.quick.push([b, b.createDiv({ cls: 'scr-swatch' })]);
    }
    this.more = btn('Pen, size and colour', () => this.togglePop('pen', this.more));
    this.dot = this.more.createDiv({ cls: 'scr-dot' });
    sep();
    this.undo = btn('Undo', withSurface(s => s.undo()), 'undo-2');
    this.redo = btn('Redo', withSurface(s => s.redo()), 'redo-2');
    sep();
    this.finger = btn('Draw with finger (two fingers scroll)', () => set('fingerDraw', !prefs.fingerDraw), 'hand');
    if (floating) {
      btn('Open as full page', withSurface(s => { if (s.opts.onOpenFull) s.opts.onOpenFull(); }), 'maximize-2');
      btn('Done writing', () => plugin.setFocus(null), 'check');
    } else this.stat = el.createDiv({ cls: 'scr-stat' });
    plugin.bars.add(this);
  }
  refresh() {
    const p = this.plugin.prefs, s = this.getSurface();
    this.pen.toggleClass('is-active', p.tool === 'pen');
    this.eraser.toggleClass('is-active', p.tool === 'eraser');
    this.select.toggleClass('is-active', p.tool === 'select');
    this.quick.forEach(([b, sw], i) => { const c = p.quick[i]; sw.style.background = cssColor(c); b.toggleClass('is-active', p.tool === 'pen' && c === p.color); });
    this.more.toggleClass('is-active', this.popKind === 'pen');
    if (this.penIcon !== p.pen) { this.pen.empty(); setIcon(this.pen, PENS[p.pen].icon); this.penIcon = p.pen; }
    const dot = Math.max(3, Math.min(20, penWidth({ size: p.size, kind: p.pen }, 0.5, 1, 1) * 2)) + 'px';
    this.dot.style.width = dot; this.dot.style.height = dot; this.dot.style.background = cssColor(p.color);
    this.dot.style.opacity = lookAlpha(p.pen);
    if (this.syncPop) this.syncPop();
    this.undo.toggleClass('is-disabled', !s || !s.undoStack.length);
    this.redo.toggleClass('is-disabled', !s || !s.redoStack.length);
    this.finger.toggleClass('is-active', p.fingerDraw);
    if (this.stat && s) this.stat.setText(s.unreadable ? 'File could not be read (left untouched)'
      : s.strokes.length + ' strokes \u00b7 slowest input ' + s.slowest.toFixed(1) + ' ms');
  }
  pickColor(c) {
    const p = this.plugin.prefs;
    if (!p.quick.includes(c)) p.quick = [c, ...p.quick].slice(0, QUICK.length);
    this.set('color', c, true);
  }
  /* ----- pop-up panels under the toolbar: all colours, line width ----- */
  togglePop(kind, anchor) {
    const same = this.popKind === kind;
    this.closePop();
    if (same) { this.refresh(); return; }
    const plugin = this.plugin, p = plugin.prefs, pop = this.pop = this.el.createDiv({ cls: 'scr-pop' });
    this.popKind = kind;
    // pen types
    const types = pop.createDiv({ cls: 'scr-pop-pens' });
    const pens = Object.keys(PENS).map(k => {
      const b = types.createDiv({ cls: 'scr-pen', attr: { 'aria-label': PENS[k].label } });
      setIcon(b.createDiv({ cls: 'scr-pen-icon' }), PENS[k].icon);
      b.createDiv({ cls: 'scr-pen-name', text: PENS[k].label });
      b.addEventListener('click', () => plugin.setPen(k));
      return [k, b];
    });
    // size: minus, slider, plus, number
    const row = pop.createDiv({ cls: 'scr-pop-row' });
    const step = d => this.set('size', Math.min(MAX_W, Math.max(MIN_W, Math.round((p.size + d) * 10) / 10)), true);
    const minus = row.createDiv({ cls: 'scr-btn', attr: { 'aria-label': 'Thinner' } }); setIcon(minus, 'minus');
    minus.addEventListener('click', () => step(-0.2));
    const slider = row.createEl('input', { type: 'range' });
    slider.min = String(MIN_W); slider.max = String(MAX_W); slider.step = '0.2';
    slider.addEventListener('input', () => this.set('size', Math.round(+slider.value * 10) / 10, true));
    const plus = row.createDiv({ cls: 'scr-btn', attr: { 'aria-label': 'Thicker' } }); setIcon(plus, 'plus');
    plus.addEventListener('click', () => step(0.2));
    const label = row.createSpan({ cls: 'scr-pop-num' });
    const sample = pop.createDiv({ cls: 'scr-pop-sample' }).createDiv();
    // colours
    const grid = pop.createDiv({ cls: 'scr-pop-grid' }), cells = [];
    for (const c of PALETTE) {
      const b = grid.createDiv({ cls: 'scr-btn', attr: { 'aria-label': c === 'ink' ? 'Ink (follows the theme)' : c } });
      b.createDiv({ cls: 'scr-swatch' }).style.background = cssColor(c);
      b.addEventListener('click', () => this.pickColor(c));
      cells.push([c, b]);
    }
    const row2 = pop.createDiv({ cls: 'scr-pop-row' });
    row2.createSpan({ text: 'Any colour' });
    const input = row2.createEl('input', { type: 'color' });
    input.value = /^#[0-9a-f]{6}$/i.test(p.color) ? p.color : '#3b82f6';
    input.addEventListener('change', () => this.pickColor(input.value.toLowerCase()));
    this.syncPop = () => {
      for (const [k, b] of pens) b.toggleClass('is-active', k === p.pen);
      for (const [c, b] of cells) b.toggleClass('is-active', c === p.color);
      slider.value = String(p.size); label.setText(p.size.toFixed(1));
      sample.style.height = Math.max(1, penWidth({ size: p.size, kind: p.pen }, 0.5, 1, 1) * 1.5) + 'px';
      sample.style.background = cssColor(p.color);
      sample.style.opacity = lookAlpha(p.pen);
    };
    // centre the panel under its button, kept inside the toolbar's width where possible
    const half = pop.offsetWidth / 2, mid = anchor.offsetLeft + anchor.offsetWidth / 2;
    pop.style.left = Math.max(Math.min(mid - half, this.el.offsetWidth - pop.offsetWidth), Math.min(0, this.el.offsetWidth - pop.offsetWidth)) + 'px';
    this.refresh();
  }
  closePop() { if (this.pop) this.pop.remove(); this.pop = null; this.popKind = null; this.syncPop = null; }
  destroy() { this.closePop(); this.plugin.bars.delete(this); this.el.remove(); }
}

/* ---------- Surface: the writing engine, used by the full page and by sections in notes ---------- */

class Surface {
  // opts: { embed, onChange(), onOpenFull() }
  constructor(plugin, host, opts) {
    this.plugin = plugin; this.prefs = plugin.prefs; this.opts = opts || {}; this.embed = !!this.opts.embed;
    this.strokes = [];
    this.bands = new Map();   // band number -> Set of strokes touching it
    this.tiles = new Map();   // band number -> { el, ctx }
    this.dirty = new Set();
    this.undoStack = []; this.redoStack = [];
    this.scale = 0; this.dpr = 1; this.heightL = 0; this.maxY = 0; this.viewH = 0;
    this.active = null; this.penDown = false; this.lastPen = -1e9;
    this.unreadable = false; this.slowest = 0; this.listeners = [];
    this.build(host);
    plugin.surfaces.add(this);
  }

  /* ----- file <-> memory ----- */
  serialize() {
    return JSON.stringify({ v: 1, w: PAGE_W, strokes: this.strokes.map(s => s.t ? { t: s.t, c: s.c, s: s.s, p: s.p } : { c: s.c, s: s.s, p: s.p }) });
  }
  load(data, reset) {
    const list = parseDoc(data);
    this.unreadable = list === null;
    this.strokes = list || [];
    this.bands.clear(); this.maxY = 0; this.heightL = 0;
    for (const s of this.strokes) this.indexStroke(s);
    if (reset) { this.undoStack = []; this.redoStack = []; if (!this.embed) this.bodyEl.scrollTop = 0; }
    this.active = null; this.clearSelection();
    this.dropTiles(); this.clearOverlay(); this.layout(); this.refreshBar();
  }
  changed() { if (this.opts.onChange) this.opts.onChange(); }

  /* ----- DOM ----- */
  on(el, type, fn, o) { el.addEventListener(type, fn, o); this.listeners.push([el, type, fn, o]); }
  build(host) {
    const root = this.root = host.createDiv({ cls: 'scr-surface ' + (this.embed ? 'scr-embed' : 'scr-full') });
    this.doc = root.ownerDocument || document;
    this.win = this.doc.defaultView || window;
    if (!this.embed) this.bar = new Bar(this.plugin, root.createDiv({ cls: 'scr-bar' }), () => this, false);
    this.bodyEl = root.createDiv({ cls: 'scr-body' });
    this.pageEl = this.bodyEl.createDiv({ cls: 'scr-page' });
    this.setBackground(this.plugin.settings.background);
    this.overlay = this.pageEl.createEl('canvas', { cls: 'scr-overlay' });
    this.overlay.width = 0; this.overlay.height = 0;
    this.octx = this.overlay.getContext('2d', { desynchronized: true });
    this.sel = null;
    this.selEl = this.pageEl.createDiv({ cls: 'scr-sel' }); this.selEl.hide();
    this.selMenu = this.pageEl.createDiv({ cls: 'scr-sel-menu' }); this.selMenu.hide();

    const el = this.pageEl;
    this.on(el, 'pointerdown', e => this.onDown(e));
    this.on(el, 'pointermove', e => this.onMove(e));
    this.on(el, 'pointerup', e => this.onUp(e, false));
    this.on(el, 'pointercancel', e => this.onUp(e, true));
    this.on(el, 'touchstart', e => this.onTouch(e), { passive: false });
    this.on(el, 'touchmove', e => this.onTouch(e), { passive: false });
    this.on(el, 'touchend', () => { this.touchY = null; });
    this.on(el, 'contextmenu', e => e.preventDefault());
    this.on(el, 'click', () => { if (!this.checkMode()) this.plugin.setFocus(this); });   // a finger tap selects the section
    if (this.embed) {
      // Keep the note editor from treating pen and taps on the section as "edit this code block".
      for (const t of ['pointerdown', 'mousedown', 'click', 'dblclick', 'contextmenu']) this.on(root, t, e => { if (!this.readOnly) e.stopPropagation(); });
    }
    // Whatever scrolls (our own page or the note around a section), keep only the visible tiles alive.
    this.on(this.doc, 'scroll', () => this.queueTiles(), { capture: true, passive: true });
    this.ro = new ResizeObserver(() => this.queueLayout());
    this.ro.observe(this.bodyEl);
    this.refreshBar();
  }
  destroy() {
    for (const [el, type, fn, o] of this.listeners) el.removeEventListener(type, fn, o);
    this.listeners = [];
    if (this.ro) this.ro.disconnect();
    this.dropTiles();
    this.overlay.width = 0; this.overlay.height = 0;
    if (this.plugin.focused === this) this.plugin.setFocus(null);
    if (this.bar) this.bar.destroy();
    this.plugin.surfaces.delete(this);
    this.root.remove();
    this.dead = true;
  }
  refreshBar() { this.plugin.refreshBars(); }
  // Paper style while editing. Reading view never shows it (see styles.css).
  setBackground(bg) {
    for (const k in BACKGROUNDS) this.pageEl.toggleClass('scr-bg-' + k, k === bg);
  }

  /* ----- layout and tiles ----- */
  // A section inside a note can be written in only while the note is in editing (Live Preview) mode.
  // Reading mode, hover previews and notes embedded in other notes show the ink but ignore pen, mouse and finger.
  checkMode() {
    const ro = this.embed && (!this.root.closest('.markdown-source-view') || !!this.root.closest('.markdown-preview-view'));
    if (ro !== this.readOnly) {
      this.readOnly = ro; this.root.toggleClass('is-readonly', ro);
      // Obsidian's own opt-out: a touch that starts on an element marked data-ignore-swipe never opens the side drawers.
      if (ro) delete this.root.dataset.ignoreSwipe; else this.root.dataset.ignoreSwipe = 'true';
      if (ro && this.plugin.focused === this) this.plugin.setFocus(null);
      if (ro) this.clearSelection();
    }
    return ro;
  }
  queueLayout() {
    if (this.layoutQueued) return;
    this.layoutQueued = true;
    this.win.requestAnimationFrame(() => { this.layoutQueued = false; if (!this.dead) this.layout(); });
  }
  layout() {
    const cw = this.bodyEl.clientWidth, ch = this.bodyEl.clientHeight;
    if (!cw || (!this.embed && !ch)) return;
    this.checkMode();
    const dpr = this.win.devicePixelRatio || 1;
    const raw = Math.min(cw, MAX_CSS_W) / PAGE_W;
    // Snap the scale so one tile is a whole number of device pixels tall: no seams between tiles.
    const scale = Math.max(1, Math.floor(BAND_H * raw * dpr)) / (BAND_H * dpr);
    if (scale !== this.scale || dpr !== this.dpr) { this.dropTiles(); this.scale = scale; this.dpr = dpr; }
    const pageW = PAGE_W * scale;
    this.pageEl.style.width = pageW + 'px';
    this.pageEl.style.marginLeft = Math.max(0, Math.round(((cw - pageW) / 2) * dpr) / dpr) + 'px';
    this.pageEl.style.setProperty('--scr-line', (LINE_GAP * scale) + 'px');
    this.viewH = ch;
    this.growPage();
    this.updateTiles();
    this.placeSel();
  }
  growPage(mayShrink) {
    if (!this.scale) return;
    if (this.maxStale) { this.maxY = 0; for (const s of this.strokes) if (s.bb[3] > this.maxY) this.maxY = s.bb[3]; this.maxStale = false; }
    let need;
    if (this.embed && this.readOnly) need = Math.max(LINE_GAP * 2, this.maxY + LINE_GAP * 0.5);                                       // reading: just the ink
    else if (this.embed) need = Math.max(LINE_GAP * 4, Math.ceil(this.maxY / LINE_GAP) * LINE_GAP + LINE_GAP * SPARE_LINES);       // editing: the ink plus spare lines
    else { const v = this.viewH / this.scale; need = Math.max(this.maxY + v * 0.8, v + LINE_GAP); }
    need = Math.ceil(need / LINE_GAP) * LINE_GAP;
    // A full page only ever grows. A section also shrinks back, but only between strokes (after erasing or undo).
    if (need > this.heightL || (mayShrink && this.embed)) this.heightL = need;
    this.pageEl.style.height = (this.heightL * this.scale) + 'px';
  }
  refit() { this.growPage(true); this.updateTiles(); }
  visibleSpan() {   // which part of the page is on screen, in CSS px from the page top
    const r = this.pageEl.getBoundingClientRect();
    return [Math.max(0, -r.top), Math.min(r.height, this.win.innerHeight - r.top)];
  }
  queueTiles() {
    if (this.tilesQueued) return;
    this.tilesQueued = true;
    this.win.requestAnimationFrame(() => { this.tilesQueued = false; if (!this.dead) this.updateTiles(); });
  }
  updateTiles() {
    if (!this.scale) return;
    const bandCss = BAND_H * this.scale;
    const [top, bot] = this.visibleSpan();
    let first = 0, last = -1;
    if (bot > top) {
      first = Math.max(0, Math.floor(top / bandCss) - 1);
      last = Math.min(Math.ceil(this.heightL / BAND_H) - 1, Math.floor(bot / bandCss) + 1);
    }
    for (const [b, t] of this.tiles) {
      if (b < first || b > last) { t.el.width = 0; t.el.height = 0; t.el.remove(); this.tiles.delete(b); }
    }
    for (let b = first; b <= last; b++) if (!this.tiles.has(b)) this.makeTile(b);
  }
  makeTile(b) {
    const bandCss = BAND_H * this.scale;
    const el = this.pageEl.createEl('canvas', { cls: 'scr-tile' });
    el.width = Math.round(PAGE_W * this.scale * this.dpr);
    el.height = Math.round(bandCss * this.dpr);
    el.style.top = (b * bandCss) + 'px';
    el.style.width = (PAGE_W * this.scale) + 'px';
    el.style.height = bandCss + 'px';
    const ctx = el.getContext('2d');
    ctx.lineCap = 'round'; ctx.lineJoin = 'round';
    this.tiles.set(b, { el, ctx });
    this.renderTile(b);
  }
  renderTile(b) {
    const t = this.tiles.get(b); if (!t) return;
    const ctx = t.ctx, k = this.scale * this.dpr;
    ctx.setTransform(1, 0, 0, 1, 0, 0);
    ctx.clearRect(0, 0, t.el.width, t.el.height);
    const set = this.bands.get(b);
    if (!set) return;
    ctx.setTransform(k, 0, 0, k, 0, -b * BAND_H * k);
    for (const s of set) if (isUnder(s)) paintStroke(ctx, s, this.resolveColor(s.c));
    for (const s of set) if (!isUnder(s)) paintStroke(ctx, s, this.resolveColor(s.c));
  }
  dropTiles() {
    for (const t of this.tiles.values()) { t.el.width = 0; t.el.height = 0; t.el.remove(); }
    this.tiles.clear(); this.dirty.clear();
  }
  redrawAll() { this.inkColor = null; for (const b of this.tiles.keys()) this.renderTile(b); }
  reindex() {   // pen looks changed: widths, and so the area each stroke covers, may be different
    this.bands.clear(); this.maxY = 0;
    for (const s of this.strokes) { computeBB(s); this.indexStroke(s); }
    this.dropTiles(); this.growPage(true); this.updateTiles();
  }
  markDirty(b) {
    this.dirty.add(b);
    if (this.dirtyQueued) return;
    this.dirtyQueued = true;
    this.win.requestAnimationFrame(() => {
      this.dirtyQueued = false;
      for (const d of this.dirty) this.renderTile(d);
      this.dirty.clear();
    });
  }
  resolveColor(c) {
    if (c !== 'ink') return c;
    if (!this.inkColor) this.inkColor = getComputedStyle(this.doc.body).getPropertyValue('--text-normal').trim() || '#222';
    return this.inkColor;
  }
  // Put the live-ink canvas over the visible part of the page and aim its coordinates at it.
  aimOverlay() {
    const dpr = this.dpr, k = this.scale * dpr;
    const [top, bot] = this.visibleSpan();
    const topCss = Math.floor(top * dpr) / dpr;
    const ow = Math.round(PAGE_W * k), oh = Math.ceil((bot - topCss) * dpr);
    if (this.overlay.width !== ow || this.overlay.height < oh) {   // grows in steps, never shrinks: no reallocation per stroke
      this.overlay.width = ow; this.overlay.height = Math.ceil(oh / 256) * 256;
      this.overlay.style.width = (ow / dpr) + 'px'; this.overlay.style.height = (this.overlay.height / dpr) + 'px';
    }
    this.overlay.style.top = topCss + 'px';
    const ctx = this.octx;
    ctx.setTransform(k, 0, 0, k, 0, -topCss * dpr);
    ctx.lineCap = 'round'; ctx.lineJoin = 'round';
    return ctx;
  }
  clearOverlay() {
    this.overlay.style.opacity = '';
    this.octx.setTransform(1, 0, 0, 1, 0, 0);
    this.octx.clearRect(0, 0, this.overlay.width, this.overlay.height);
  }

  /* ----- stroke store ----- */
  bandRange(s) { return [Math.max(0, Math.floor(s.bb[1] / BAND_H)), Math.max(0, Math.floor(s.bb[3] / BAND_H))]; }
  indexStroke(s) {
    const [b0, b1] = this.bandRange(s);
    for (let b = b0; b <= b1; b++) {
      let set = this.bands.get(b);
      if (!set) this.bands.set(b, set = new Set());
      set.add(s);
    }
    if (s.bb[3] > this.maxY) this.maxY = s.bb[3];
  }
  addStrokes(list, paintNow) {
    for (const s of list) {
      this.strokes.push(s);
      this.indexStroke(s);
      const [b0, b1] = this.bandRange(s);
      for (let b = b0; b <= b1; b++) {
        if (!paintNow) { this.markDirty(b); continue; }
        const t = this.tiles.get(b); if (!t) continue;
        if (isUnder(s)) { this.renderTile(b); continue; }   // goes under the ink, so the tile is redrawn
        const k = this.scale * this.dpr;
        t.ctx.setTransform(k, 0, 0, k, 0, -b * BAND_H * k);
        paintStroke(t.ctx, s, this.resolveColor(s.c));   // added on top; nothing else is redrawn
      }
    }
    this.growPage(); this.updateTiles();
  }
  delStrokes(list) {
    const gone = new Set(list);
    this.strokes = this.strokes.filter(s => !gone.has(s));
    for (const s of list) {
      const [b0, b1] = this.bandRange(s);
      for (let b = b0; b <= b1; b++) {
        const set = this.bands.get(b);
        if (set) { set.delete(s); if (!set.size) this.bands.delete(b); }
        this.markDirty(b);
      }
    }
    this.maxStale = true;
  }
  bandsOf(s) { const [b0, b1] = this.bandRange(s), out = []; for (let b = b0; b <= b1; b++) out.push(b); return out; }
  setStrokes(arr) {   // undo / redo of an erase: put back the exact earlier list, in order
    this.strokes = arr.slice(); this.bands.clear(); this.maxY = 0;
    for (const s of this.strokes) this.indexStroke(s);
    for (const b of this.tiles.keys()) this.markDirty(b);
  }
  replaceStroke(old, pieces) {   // partial erase: the pieces take the old stroke's place, so layering stays the same
    const i = this.strokes.indexOf(old); if (i < 0) return;
    this.strokes.splice(i, 1, ...pieces);
    const touched = new Set(this.bandsOf(old));
    for (const n of pieces) for (const b of this.bandsOf(n)) touched.add(b);
    for (const b of touched) {   // rebuild these bands in drawing order
      const set = new Set();
      for (const t of this.strokes) { const [b0, b1] = this.bandRange(t); if (b >= b0 && b <= b1) set.add(t); }
      if (set.size) this.bands.set(b, set); else this.bands.delete(b);
      this.markDirty(b);
    }
    this.maxStale = true;
  }
  pushUndo(op) {
    this.undoStack.push(op);
    if (this.undoStack.length > 300) this.undoStack.shift();
    this.redoStack.length = 0;
  }
  undo() {
    this.clearSelection();
    const op = this.undoStack.pop(); if (!op) return;
    if (op.t === 'add') this.delStrokes(op.strokes); else this.setStrokes(op.before);
    this.redoStack.push(op); this.refit(); this.changed(); this.refreshBar();
  }
  redo() {
    this.clearSelection();
    const op = this.redoStack.pop(); if (!op) return;
    if (op.t === 'add') this.addStrokes(op.strokes, false); else this.setStrokes(op.after);
    this.undoStack.push(op); this.refit(); this.changed(); this.refreshBar();
  }

  /* ----- input ----- */
  point(a, ev) {   // screen position -> page units, kept inside the page
    const x = (ev.clientX - a.left) / this.scale, y = (ev.clientY - a.top) / this.scale;
    return [x < 0 ? 0 : x > PAGE_W ? PAGE_W : x, y < 0 ? 0 : y > this.heightL - 1 ? this.heightL - 1 : y];
  }
  onDown(e) {
    if (e.target && e.target.closest && e.target.closest('.scr-sel-menu')) return;   // taps on the selection menu are its own
    if (this.active || this.unreadable || !this.scale || this.checkMode()) return;
    const now = performance.now(), type = e.pointerType, prefs = this.prefs;
    if (type === 'touch') {
      if (!prefs.fingerDraw) return;                             // finger scrolls natively
      if (this.penDown || now - this.lastPen < 500) return;      // palm while writing
    } else if (type === 'mouse') {
      if (e.button !== 0) return;
    } else {
      this.penDown = true; this.lastPen = now;
    }
    e.preventDefault();
    this.plugin.closePops();
    this.plugin.setFocus(this);
    try { this.pageEl.setPointerCapture(e.pointerId); } catch (err) { /* older WebViews */ }
    const rect = this.pageEl.getBoundingClientRect();
    const erasing = prefs.tool === 'eraser' || (type === 'pen' && (e.buttons & 34) !== 0);  // pen eraser tip or side button
    const a = this.active = { id: e.pointerId, type, erasing, left: rect.left, top: rect.top, p: [], before: null, erased: false, st: null, c: prefs.color, s: prefs.size, t: prefs.pen };
    if (!erasing && prefs.tool === 'select') { this.selDown(e, type, rect); return; }
    const [x, y] = this.point(a, e);
    this.root.addClass('is-inking');
    if (erasing) { a.before = this.strokes.slice(); this.aimOverlay(); this.eraseAt(a, x, y); this.showEraser(x, y); return; }
    const ctx = this.aimOverlay();
    ctx.strokeStyle = ctx.fillStyle = this.resolveColor(a.c);
    a.st = { size: a.s, kind: a.t };
    this.overlay.style.opacity = lookAlpha(a.t);   // see-through pens: drawn solid, shown see-through
    ctx.lineCap = LOOKS[a.t] ? LOOKS[a.t].cap : 'round';
    const pr = this.pressure(e);
    a.p.push(x, y, pr);
    inkBegin(ctx, a.st, x, y, pr);
    if (type === 'pen' && this.plugin.settings.shapes) { a.hold = true; this.holdFrom(a, x, y); }
  }
  /* ----- shapes: hold the pen still at the end of a stroke and it snaps to a clean shape ----- */
  holdFrom(a, x, y) {   // the pen moved: restart the stillness clock from here
    a.hx = x; a.hy = y;
    clearTimeout(a.holdT);
    a.holdT = setTimeout(() => this.snapShape(a), this.plugin.settings.shapeHold);
  }
  snapShape(a) {
    if (this.active !== a || a.shape) return;
    const p = a.p, xy = [];
    for (let i = 0; i < p.length; i += 3) xy.push(p[i], p[i + 1]);
    let r = null;
    try { r = recognizeShape(xy); } catch (err) { console.error('Scribble: shape recognition failed', err); }
    if (!r) return;   // not a shape: the stroke stays as drawn
    a.shape = { kind: r.kind, base: r.xy, xy: r.xy, ax: r.ax, ay: r.ay, rx: a.hx - r.ax, ry: a.hy - r.ay };
    this.drawLiveShape(a);
  }
  adjustShape(a, x, y) {   // still holding after the snap: scale and turn the shape around its anchor to follow the pen
    const S = a.shape, r0 = Math.hypot(S.rx, S.ry);
    if (r0 < 3) return;
    const vx = x - S.ax, vy = y - S.ay;
    let k = Math.hypot(vx, vy) / r0, rot = Math.atan2(vy, vx) - Math.atan2(S.ry, S.rx);
    if (k < 0.05) k = 0.05;
    if (S.kind === 'line' || S.kind === 'arrow') {   // keep lines on 0/45/90 degrees when close
      const b = S.base, n = b.length;
      const end = S.kind === 'line' ? [b[n - 2], b[n - 1]] : [S.ax + S.rx, S.ay + S.ry];
      const a0 = Math.atan2(end[1] - S.ay, end[0] - S.ax);
      rot = snapAngle(a0 + rot, Math.PI / 4, 5 * Math.PI / 180) - a0;
    }
    const c = Math.cos(rot) * k, s = Math.sin(rot) * k, b = S.base, out = new Array(b.length);
    for (let i = 0; i < b.length; i += 2) {
      const u = b[i] - S.ax, v = b[i + 1] - S.ay;
      out[i] = S.ax + u * c - v * s; out[i + 1] = S.ay + u * s + v * c;
    }
    S.xy = out;
    if (S.queued) return;
    S.queued = true;
    this.win.requestAnimationFrame(() => { S.queued = false; if (this.active === a && a.shape === S) this.drawLiveShape(a); });
  }
  shapePoints(xy) {   // flat [x, y] -> stored [x, y, pressure]: even width
    const p = [];
    for (let i = 0; i < xy.length; i += 2) p.push(Math.round(xy[i] * 10) / 10, Math.round(xy[i + 1] * 10) / 10, 0.5);
    return p;
  }
  drawLiveShape(a) {
    this.octx.setTransform(1, 0, 0, 1, 0, 0);
    this.octx.clearRect(0, 0, this.overlay.width, this.overlay.height);
    const ctx = this.aimOverlay();
    ctx.strokeStyle = ctx.fillStyle = this.resolveColor(a.c);
    drawStroke(ctx, { t: a.t, s: a.s, p: this.shapePoints(a.shape.xy) });
  }
  pressure(e) {
    if (e.pointerType !== 'pen') return 0.5;
    return e.pressure > 0 ? Math.min(1, e.pressure) : 0.5;
  }
  onMove(e) {
    const a = this.active;
    if (!a || e.pointerId !== a.id) return;
    if (a.select) { this.selMove(a, e); return; }
    const t0 = performance.now();
    if (a.type === 'pen') this.lastPen = t0;
    const evs = (e.getCoalescedEvents && e.getCoalescedEvents()) || [];
    const n = evs.length || 1;
    for (let i = 0; i < n; i++) {
      const ev = evs.length ? evs[i] : e;
      const [x, y] = this.point(a, ev);
      if (a.erasing) { this.eraseAt(a, x, y); a.ex = x; a.ey = y; continue; }
      if (a.shape) { if (i === n - 1) this.adjustShape(a, x, y); continue; }
      if (a.hold) { const tol = SHAPE_STILL_PX / this.scale, hx = x - a.hx, hy = y - a.hy; if (hx * hx + hy * hy > tol * tol) this.holdFrom(a, x, y); }
      const dx = x - a.st.px, dy = y - a.st.py;
      if (dx * dx + dy * dy < 0.36) continue;
      const pr = this.pressure(ev);
      a.p.push(x, y, pr);
      inkMove(this.octx, a.st, x, y, pr);
    }
    if (a.erasing && a.ex !== undefined) this.showEraser(a.ex, a.ey);
    const dt = performance.now() - t0;
    if (dt > this.slowest) this.slowest = dt;
  }
  onUp(e, cancelled) {
    const a = this.active;
    if (e.pointerType === 'pen') { this.penDown = false; this.lastPen = performance.now(); }
    if (!a || e.pointerId !== a.id) return;
    this.endStroke(cancelled && a.p.length < 6);
  }
  endStroke(discard) {
    const a = this.active; if (!a) return;
    this.active = null;
    clearTimeout(a.holdT);
    this.root.removeClass('is-inking');
    if (a.select) { this.selEnd(a, discard); return; }
    if (a.erasing) {
      this.clearOverlay();
      if (a.erased) { this.pushUndo({ t: 'swap', before: a.before, after: this.strokes.slice() }); this.refit(); this.changed(); }
      this.refreshBar(); return;
    }
    if (discard) { this.clearOverlay(); return; }
    const p = a.p;
    for (let i = 0; i < p.length; i += 3) {
      p[i] = Math.round(p[i] * 10) / 10; p[i + 1] = Math.round(p[i + 1] * 10) / 10; p[i + 2] = Math.round(p[i + 2] * 100) / 100;
    }
    const s = { t: a.t, c: a.c, s: a.s, p };
    computeBB(s);
    if (a.shape) {
      // Like Apple: one undo turns the shape back into what was drawn, a second removes it.
      const shape = { t: a.t, c: a.c, s: a.s, p: this.shapePoints(a.shape.xy) };
      computeBB(shape);
      const before = this.strokes.slice(); before.push(s);
      this.addStrokes([shape], true);
      this.clearOverlay();
      this.pushUndo({ t: 'add', strokes: [s] });
      this.pushUndo({ t: 'swap', before, after: this.strokes.slice() });
      this.changed(); this.refreshBar();
      return;
    }
    this.addStrokes([s], true);   // bake into the tiles ...
    this.clearOverlay();          // ... and drop the live copy in the same frame
    this.pushUndo({ t: 'add', strokes: [s] });
    this.changed();               // the file is written a moment later, not now
    this.refreshBar();
  }
  eraseAt(a, x, y) {
    const set = this.plugin.settings, r = set.eraserSize || ERASER_R, partial = set.eraser !== 'stroke';
    const b0 = Math.max(0, Math.floor((y - r) / BAND_H)), b1 = Math.max(0, Math.floor((y + r) / BAND_H));
    let found = null;
    for (let b = b0; b <= b1; b++) {
      const bs = this.bands.get(b); if (!bs) continue;
      for (const s of bs) if (hits(s, x, y, r) && !(found && found.includes(s))) (found || (found = [])).push(s);
    }
    if (!found) return;
    if (!partial) { this.delStrokes(found); a.erased = true; return; }
    for (const s of found) {
      const pieces = cutStroke(s, x, y, r);
      if (pieces) { this.replaceStroke(s, pieces); a.erased = true; }
    }
  }
  showEraser(x, y) {   // the eraser's circle under the pen
    const ctx = this.octx, r = this.plugin.settings.eraserSize || ERASER_R;
    ctx.save(); ctx.setTransform(1, 0, 0, 1, 0, 0); ctx.clearRect(0, 0, this.overlay.width, this.overlay.height); ctx.restore();
    ctx.beginPath(); ctx.arc(x, y, r, 0, 6.2832);
    ctx.lineWidth = 1.2 / this.scale; ctx.strokeStyle = this.resolveColor('ink'); ctx.globalAlpha = 0.45; ctx.stroke(); ctx.globalAlpha = 1;
  }
  /* ----- leaving a section: empty space above the first ink is removed -----
   * Whole lines only, so writing stays on its ruled line. One undo step. Sections only, never full pages. */
  trimTop() {
    if (!this.embed || this.dead || this.unreadable || this.active || !this.strokes.length) return;
    let top = Infinity;
    for (const s of this.strokes) if (s.bb[1] < top) top = s.bb[1];
    const k = Math.floor(Math.max(0, top) / LINE_GAP);
    if (k < 1) return;
    const before = this.strokes.slice(), after = before.map(s => shifted(s, 0, -k * LINE_GAP));
    this.setStrokes(after);
    this.pushUndo({ t: 'swap', before, after: after.slice() });
    this.refit(); this.changed(); this.refreshBar();
  }

  /* ----- selection: lasso around ink, then move, copy, cut, recolour or delete it ----- */
  accent() { return getComputedStyle(this.doc.body).getPropertyValue('--interactive-accent').trim() || '#7c5cff'; }
  selDown(e, type, rect) {
    const a = this.active = { id: e.pointerId, type, select: true, left: rect.left, top: rect.top, p: [] };
    const [x, y] = this.point(a, e);
    a.x0 = x; a.y0 = y; a.dx = 0; a.dy = 0;
    this.root.addClass('is-inking');
    this.selMenu.hide();
    const b = this.sel && this.sel.bb, pad = 8;
    if (b && x >= b[0] - pad && x <= b[2] + pad && y >= b[1] - pad && y <= b[3] + pad) {   // start inside the selection: move it
      a.drag = true; a.before = this.strokes.slice(); a.moving = this.sel.strokes;
      this.delStrokes(a.moving);
      a.ctx = this.aimOverlay(); this.paintDrag(a);
      return;
    }
    this.clearSelection();
    a.p.push(x, y);
    a.ctx = this.aimOverlay();
  }
  selMove(a, e) {
    const evs = (e.getCoalescedEvents && e.getCoalescedEvents()) || [];
    const list = evs.length ? evs : [e];
    for (const ev of list) {
      const [x, y] = this.point(a, ev);
      if (a.drag) { a.dx = x - a.x0; a.dy = y - a.y0; continue; }
      const n = a.p.length, lx = a.p[n - 2], ly = a.p[n - 1];
      if ((x - lx) * (x - lx) + (y - ly) * (y - ly) >= 2.25) a.p.push(x, y);
    }
    if (a.queued) return;
    a.queued = true;
    this.win.requestAnimationFrame(() => { a.queued = false; if (this.active !== a) return; if (a.drag) this.paintDrag(a); else this.paintLasso(a); });
  }
  clampDrag(a) {   // keep moved ink on the page
    const b = this.sel.bb;
    a.dx = Math.max(-b[0], Math.min(PAGE_W - b[2], a.dx));
    a.dy = Math.max(-b[1], a.dy);
  }
  paintDrag(a) {
    this.clampDrag(a);
    const ctx = a.ctx;
    ctx.save(); ctx.setTransform(1, 0, 0, 1, 0, 0); ctx.clearRect(0, 0, this.overlay.width, this.overlay.height); ctx.restore();
    ctx.save(); ctx.translate(a.dx, a.dy);
    for (const s of a.moving) if (isUnder(s)) paintStroke(ctx, s, this.resolveColor(s.c));
    for (const s of a.moving) if (!isUnder(s)) paintStroke(ctx, s, this.resolveColor(s.c));
    ctx.restore();
    this.selEl.style.transform = `translate(${a.dx * this.scale}px, ${a.dy * this.scale}px)`;
  }
  paintLasso(a) {
    const ctx = a.ctx, p = a.p;
    ctx.save(); ctx.setTransform(1, 0, 0, 1, 0, 0); ctx.clearRect(0, 0, this.overlay.width, this.overlay.height); ctx.restore();
    if (p.length < 4) return;
    ctx.save();
    ctx.lineWidth = 1.5 / this.scale; ctx.setLineDash([6 / this.scale, 5 / this.scale]);
    ctx.strokeStyle = this.accent(); ctx.fillStyle = this.accent(); ctx.lineCap = 'round';
    ctx.beginPath(); ctx.moveTo(p[0], p[1]);
    for (let i = 2; i < p.length; i += 2) ctx.lineTo(p[i], p[i + 1]);
    ctx.stroke();
    ctx.globalAlpha = 0.06; ctx.closePath(); ctx.fill();
    ctx.restore();
  }
  selEnd(a, cancelled) {
    this.clearOverlay();
    if (a.drag) {
      this.selEl.style.transform = '';
      this.clampDrag(a);
      if (Math.abs(a.dx) < 0.5 && Math.abs(a.dy) < 0.5) {   // just a tap on the selection: put it back
        this.setStrokes(a.before); this.placeSel(); return;
      }
      const moved = new Map(a.moving.map(s => [s, shifted(s, a.dx, a.dy)]));
      const after = a.before.map(s => moved.get(s) || s);
      this.setStrokes(after);
      this.pushUndo({ t: 'swap', before: a.before, after: after.slice() });
      this.select([...moved.values()]);
      this.refit(); this.changed(); this.refreshBar();
      return;
    }
    if (cancelled) return;
    const p = a.p;
    let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
    for (let i = 0; i < p.length; i += 2) { x0 = Math.min(x0, p[i]); x1 = Math.max(x1, p[i]); y0 = Math.min(y0, p[i + 1]); y1 = Math.max(y1, p[i + 1]); }
    if (x1 - x0 < 6 && y1 - y0 < 6) {   // a tap: pick the stroke under it, or offer to paste here
      let hit = null;
      for (let i = this.strokes.length - 1; i >= 0 && !hit; i--) if (hits(this.strokes[i], a.x0, a.y0, 6)) hit = this.strokes[i];
      if (hit) this.select([hit]);
      else if (this.plugin.clip) this.showPaste(a.x0, a.y0);
      return;
    }
    const found = [];
    for (const s of this.strokes) {
      const b = s.bb;
      if (b[2] < x0 || b[0] > x1 || b[3] < y0 || b[1] > y1) continue;
      let inside = 0, n = 0;
      for (let i = 0; i < s.p.length; i += 3) { n++; if (inPoly(s.p[i], s.p[i + 1], p)) inside++; }
      if (inside * 2 >= n) found.push(s);   // most of the stroke is inside the loop
    }
    if (found.length) this.select(found);
  }
  select(list) {
    this.sel = { strokes: list, bb: unionBB(list) };
    this.placeSel();
  }
  clearSelection() {
    if (!this.selEl) return;
    this.sel = null; this.pasteAt = false; this.selEl.hide(); this.selMenu.hide(); this.selEl.style.transform = '';
  }
  placeSel() {
    if (!this.sel || !this.scale) { if (this.selEl) { this.selEl.hide(); if (!this.pasteAt) this.selMenu.hide(); } return; }
    const k = this.scale, b = this.sel.bb, pad = 4;
    const st = this.selEl.style;
    st.left = (b[0] * k - pad) + 'px'; st.top = (b[1] * k - pad) + 'px';
    st.width = ((b[2] - b[0]) * k + pad * 2) + 'px'; st.height = ((b[3] - b[1]) * k + pad * 2) + 'px';
    this.selEl.show();
    this.buildMenu('sel');
    this.placeMenu(b[0] * k, b[1] * k - pad, (b[2] - b[0]) * k, b[3] * k + pad);
  }
  placeMenu(left, top, width, bottom) {
    const m = this.selMenu; m.show();
    const mw = m.offsetWidth || 180, mh = m.offsetHeight || 40, pw = PAGE_W * this.scale;
    let y = top - mh - 8;
    if (y < 0) y = bottom + 8;
    m.style.top = y + 'px';
    m.style.left = Math.max(4, Math.min(pw - mw - 4, left + width / 2 - mw / 2)) + 'px';
  }
  buildMenu(mode) {
    const m = this.selMenu; m.empty(); this.pasteAt = mode === 'paste';
    const btn = (label, icon, fn) => {
      const b = m.createDiv({ cls: 'scr-btn', attr: { 'aria-label': label } });
      setIcon(b, icon); b.createSpan({ cls: 'scr-sel-label', text: label });
      b.addEventListener('click', e => { e.stopPropagation(); fn(); });
      return b;
    };
    if (mode === 'paste') { btn('Paste', 'clipboard-paste', () => this.paste(this.pasteX, this.pasteY)); return; }
    btn('Copy', 'copy', () => { this.copySel(); new Notice('Copied ' + this.sel.strokes.length + (this.sel.strokes.length === 1 ? ' stroke' : ' strokes'), 1500); });
    btn('Cut', 'scissors', () => { this.copySel(); this.deleteSel(); });
    const colour = btn('Colour', 'palette', () => {
      if (this.colourRow) { this.colourRow.remove(); this.colourRow = null; return; }
      const row = this.colourRow = m.createDiv({ cls: 'scr-sel-colours' });
      for (const c of PALETTE) {
        const sw = row.createDiv({ cls: 'scr-btn', attr: { 'aria-label': c === 'ink' ? 'Ink' : c } });
        sw.createDiv({ cls: 'scr-swatch' }).style.background = cssColor(c);
        sw.addEventListener('click', e => { e.stopPropagation(); this.recolourSel(c); });
      }
    });
    colour.addClass('scr-sel-colour');
    this.colourRow = null;
    btn('Delete', 'trash-2', () => this.deleteSel());
  }
  showPaste(x, y) {
    this.pasteX = x; this.pasteY = y;
    this.buildMenu('paste');
    const k = this.scale;
    this.placeMenu(x * k, y * k, 0, y * k);
  }
  copySel() {
    const b = this.sel.bb;
    this.plugin.clip = { w: b[2] - b[0], h: b[3] - b[1], strokes: this.sel.strokes.map(s => shifted(s, -b[0], -b[1])) };
  }
  deleteSel() {
    const gone = new Set(this.sel.strokes), before = this.strokes.slice(), after = before.filter(s => !gone.has(s));
    this.clearSelection();
    this.setStrokes(after);
    this.pushUndo({ t: 'swap', before, after: after.slice() });
    this.refit(); this.changed(); this.refreshBar();
  }
  recolourSel(c) {
    const map = new Map(this.sel.strokes.map(s => { const n = { c, s: s.s, p: s.p, bb: s.bb }; if (s.t) n.t = s.t; return [s, n]; }));
    const before = this.strokes.slice(), after = before.map(s => map.get(s) || s);
    this.setStrokes(after);
    this.pushUndo({ t: 'swap', before, after: after.slice() });
    this.select([...map.values()]);
    this.changed(); this.refreshBar();
  }
  paste(x, y) {
    const clip = this.plugin.clip; if (!clip) return;
    let dx = x - clip.w / 2, dy = y - clip.h / 2;
    dx = Math.max(0, Math.min(PAGE_W - clip.w, dx)); dy = Math.max(0, dy);
    const list = clip.strokes.map(s => shifted(s, dx, dy));
    this.selMenu.hide(); this.pasteAt = false;
    this.addStrokes(list, false);
    this.pushUndo({ t: 'add', strokes: list });
    this.select(list);
    this.changed(); this.refreshBar();
  }
  onTouch(e) {
    // Android reports the pen as a touch too. Stop the page from scrolling under the pen or the palm.
    if (this.readOnly) return;   // reading mode: pen and finger just scroll the note
    const stylus = e.touches.length && e.touches[0].touchType === 'stylus';
    if (this.penDown || stylus || performance.now() - this.lastPen < 250) { if (e.cancelable) e.preventDefault(); return; }
    if (!this.prefs.fingerDraw) return;
    if (e.cancelable) e.preventDefault();
    if (e.touches.length >= 2) {   // two fingers scroll while finger-drawing is on
      if (this.active && this.active.type === 'touch') this.endStroke(true);
      const y = (e.touches[0].clientY + e.touches[1].clientY) / 2;
      const scroller = this.embed ? this.root.closest('.cm-scroller, .markdown-preview-view') : this.bodyEl;
      if (scroller && this.touchY != null && e.type === 'touchmove') scroller.scrollTop -= y - this.touchY;
      this.touchY = y;
    } else this.touchY = null;
  }
}

/* ---------- full-page view (.scribble file opened in its own tab) ---------- */

class ScribbleView extends TextFileView {
  constructor(leaf, plugin) { super(leaf); this.plugin = plugin; }
  getViewType() { return VIEW_TYPE; }
  getDisplayText() { return this.file ? this.file.basename : 'Scribble'; }
  getIcon() { return 'pencil'; }
  ensure() {
    if (this.surface) return this.surface;
    this.contentEl.empty(); this.contentEl.addClass('scr-host');
    return this.surface = new Surface(this.plugin, this.contentEl, { onChange: () => this.requestSave(), onBack: () => this.goBack() });
  }
  async onOpen() { this.ensure(); }
  async goBack() {
    await this.save();
    const h = this.leaf.history;   // not a public API, so fall back to Obsidian's own command if it is missing
    if (h && h.backHistory && typeof h.back === 'function') { if (h.backHistory.length) h.back(); else this.leaf.detach(); }
    else this.app.commands.executeCommandById('app:go-back');
  }
  async onClose() { if (this.surface) { this.surface.destroy(); this.surface = null; } }
  getViewData() {
    const s = this.surface;
    return !s || s.unreadable ? this.data : s.serialize();   // never overwrite a file we failed to parse
  }
  setViewData(data, clear) { this.ensure().load(data, clear); }
  clear() { if (this.surface) this.surface.load('', true); }
}

/* ---------- handwritten section inside a note ---------- */

class ScribbleEmbed extends MarkdownRenderChild {
  constructor(el, plugin, link, sourcePath) { super(el); this.plugin = plugin; this.link = link; this.sourcePath = sourcePath; }
  async onload() {
    const app = this.plugin.app;
    let f = this.link ? app.vault.getAbstractFileByPath(normalizePath(this.link)) : null;
    if (!(f instanceof TFile) && this.link) f = app.metadataCache.getFirstLinkpathDest(this.link, this.sourcePath);   // moved file: find it by name
    if (!(f instanceof TFile) || f.extension !== EXT) {
      this.containerEl.createDiv({ cls: 'scr-missing', text: 'Handwritten section not found: ' + (this.link || '(no file given)') });
      return;
    }
    this.file = f;
    this.last = await app.vault.read(f);
    if (this.gone) return;
    this.surface = new Surface(this.plugin, this.containerEl, {
      embed: true,
      onChange: () => this.queueSave(),
      onOpenFull: async () => {
        clearTimeout(this.timer); await this.save();          // make sure the page opens with the latest ink
        const leaf = app.workspace.getMostRecentLeaf() || app.workspace.getLeaf(false);
        await leaf.openFile(f);                               // same tab: Back returns to this note
      },
    });
    this.surface.load(this.last, true);
    // The same section may be open elsewhere (another note, the full page, another device via sync).
    this.registerEvent(app.vault.on('modify', async file => {
      if (file !== this.file || !this.surface) return;
      const d = await app.vault.read(file);
      if (d === this.last || !this.surface) return;
      this.last = d; clearTimeout(this.timer); this.timer = null;
      this.surface.load(d, false);
    }));
  }
  queueSave() { clearTimeout(this.timer); this.timer = setTimeout(() => this.save(), 1500); }
  async save() {
    this.timer = null;
    if (!this.surface || this.surface.unreadable) return;
    const d = this.surface.serialize();
    if (d === this.last) return;
    this.last = d;
    try { await this.plugin.app.vault.modify(this.file, d); }
    catch (e) { console.error('Scribble: save failed', e); new Notice('Scribble: could not save ' + this.file.path); }
  }
  onunload() {
    this.gone = true;
    if (this.surface && this.plugin.focused === this.surface) this.plugin.setFocus(null);   // tidies the top; saved just below
    if (this.timer) { clearTimeout(this.timer); this.save(); }   // flush pending ink before the section goes away
    if (this.surface) { this.surface.destroy(); this.surface = null; }
  }
}

class ScribbleSettings extends PluginSettingTab {
  constructor(app, plugin) { super(app, plugin); this.plugin = plugin; }
  display() {
    const el = this.containerEl, plugin = this.plugin;
    el.empty();
    new Setting(el)
      .setName('Canvas background')
      .setDesc('Paper style while you write. Reading view always shows only the ink.')
      .addDropdown(dd => {
        for (const k in BACKGROUNDS) dd.addOption(k, BACKGROUNDS[k]);
        dd.setValue(plugin.settings.background).onChange(v => plugin.setBackground(v));
      });
    new Setting(el).setName('Eraser').setHeading();
    new Setting(el)
      .setName('Eraser type')
      .setDesc('Partial cuts through ink like a real eraser. Whole stroke removes each stroke it touches in one go.')
      .addDropdown(dd => {
        dd.addOption('partial', 'Partial').addOption('stroke', 'Whole stroke');
        dd.setValue(plugin.settings.eraser).onChange(v => { plugin.settings.eraser = v; plugin.saveData(plugin.settings); });
      });
    new Setting(el)
      .setName('Eraser size')
      .setDesc('Size of the eraser circle. It is shown under the pen while erasing.')
      .addSlider(sl => sl.setLimits(4, 60, 1).setValue(plugin.settings.eraserSize).setDynamicTooltip()
        .onChange(v => { plugin.settings.eraserSize = v; plugin.saveData(plugin.settings); }));
    new Setting(el).setName('Shapes').setHeading();
    new Setting(el)
      .setName('Recognise shapes')
      .setDesc('Draw a line, circle, rectangle, triangle, arrow or arc with the pen and hold it still for a moment: it snaps to a clean shape. Keep holding and move to resize or turn it. Undo brings back what you drew.')
      .addToggle(t => t.setValue(plugin.settings.shapes).onChange(v => { plugin.settings.shapes = v; plugin.saveData(plugin.settings); }));
    new Setting(el)
      .setName('Hold time')
      .setDesc('How long to hold the pen still before the shape snaps, in milliseconds.')
      .addSlider(sl => sl.setLimits(200, 1500, 50).setValue(plugin.settings.shapeHold).setDynamicTooltip()
        .onChange(v => { plugin.settings.shapeHold = v; plugin.saveData(plugin.settings); }));
    new Setting(el).setName('Pens').setHeading()
      .setDesc('How each pen looks. Changes apply to everything already written with that pen, on every device.');
    for (const kind in LOOK_DEFAULTS) this.penSection(el, kind);
  }
  penSection(el, kind) {
    const plugin = this.plugin, L = () => LOOKS[kind];
    new Setting(el).setName(PENS[kind].label).setHeading()
      .addExtraButton(b => b.setIcon('rotate-ccw').setTooltip('Back to default').onClick(() => { plugin.setLook(kind); this.display(); }));
    const preview = el.createEl('canvas', { cls: 'scr-look-preview' });
    const redraw = () => drawPreview(preview, kind, plugin);
    const slider = (name, desc, key, min, max, step, toUi, fromUi) => new Setting(el).setName(name).setDesc(desc).addSlider(sl => sl
      .setLimits(min, max, step).setValue(toUi(L()[key])).setDynamicTooltip()
      .onChange(v => { plugin.setLook(kind, key, fromUi(v)); redraw(); }));
    const pct = v => Math.round(v * 100), frac = v => v / 100;
    slider('Thickness', 'How wide this pen draws at the same size (percent of normal).', 'width', 30, 300, 5, pct, frac);
    slider('Pressure', 'How much pressing harder makes the line wider. 0 = not at all.', 'pressure', 0, 100, 1, pct, frac);
    slider('Smoothing', 'How gently the width changes. 0 = follows the pen instantly.', 'smoothing', 0, 95, 1, pct, frac);
    slider('Opacity', 'Below 100 the ink is see-through.', 'opacity', 10, 100, 1, pct, frac);
    if (LOOK_DEFAULTS[kind].angle !== undefined) {
      slider('Nib angle', 'Angle of the broad nib edge, in degrees. Lines along the edge are thinnest. Negative values suit left-handed writing.', 'angle', -90, 90, 1, v => v, v => v);
      slider('Thinnest line', 'The thinnest stroke, as a percent of the widest. 100 = no thick-and-thin effect.', 'hairline', 0, 100, 1, pct, frac);
    }
    new Setting(el).setName('Line ends').setDesc('Rounded, or square like a chisel tip.').addDropdown(dd => dd
      .addOption('round', 'Rounded').addOption('square', 'Square')
      .setValue(L().cap).onChange(v => { plugin.setLook(kind, 'cap', v); redraw(); }));
    new Setting(el).setName('Draw under other ink').setDesc('Keeps this pen beneath writing, like a highlighter.').addToggle(t => t
      .setValue(L().under).onChange(v => { plugin.setLook(kind, 'under', v); redraw(); }));
    redraw();
  }
}

// A sample word-like loop with light-heavy-light pressure, drawn with the pen's current look.
function drawPreview(canvas, kind, plugin) {
  if (!canvas.getContext) return;
  const W = 300, H = 76, dpr = window.devicePixelRatio || 1;
  canvas.width = W * dpr; canvas.height = H * dpr; canvas.style.width = W + 'px'; canvas.style.height = H + 'px';
  const ctx = canvas.getContext('2d'); if (!ctx) return;
  ctx.setTransform(1, 0, 0, 1, 0, 0); ctx.clearRect(0, 0, canvas.width, canvas.height);
  const pen = (plugin.prefs.pens && plugin.prefs.pens[kind]) || PENS[kind].def;
  const sc = 1.6, p = [];
  for (let i = 0; i <= 160; i++) {
    const t = i / 160, u = t * 6 * Math.PI;
    p.push((14 + 26 * u - 30 * Math.sin(u)) / sc, (40 - 26 * Math.cos(u)) / sc, Math.round((0.2 + 0.7 * Math.sin(Math.PI * t)) * 100) / 100);
  }
  const s = { t: kind, s: pen.size, p }; computeBB(s);
  const col = pen.color === 'ink' ? (getComputedStyle(document.body).getPropertyValue('--text-normal').trim() || '#222') : pen.color;
  ctx.setTransform(dpr * sc, 0, 0, dpr * sc, 0, 0);
  paintStroke(ctx, s, col);
  if (LOOKS[kind].under) {   // a word on top, so "under other ink" can be seen
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0); ctx.font = '600 18px sans-serif'; ctx.fillStyle = getComputedStyle(document.body).getPropertyValue('--text-normal').trim() || '#222'; ctx.fillText('highlighted text', 40, 46); }
}

class PickScribble extends FuzzySuggestModal {
  constructor(app, files, onPick) { super(app); this.files = files; this.onPick = onPick; this.setPlaceholder('Choose a handwritten section to insert'); }
  getItems() { return this.files; }
  getItemText(f) { return f.path.replace(/\.scribble$/, ''); }
  onChooseItem(f) { this.onPick(f); }
}

module.exports = class ScribblePlugin extends Plugin {
  async onload() {
    this.prefs = { tool: 'pen', pen: 'ball', pens: {}, color: 'ink', size: 2.8, fingerDraw: false, quick: QUICK.slice() };   // shared by every page and section
    try {   // pen settings are remembered per device (not in the synced plugin data, which would cause sync conflicts)
      const saved = JSON.parse(window.localStorage.getItem(PREFS_KEY) || '{}');
      if (typeof saved.color === 'string') this.prefs.color = saved.color;
      if (saved.size >= MIN_W && saved.size <= MAX_W) this.prefs.size = saved.size;
      if (Array.isArray(saved.quick) && saved.quick.length === QUICK.length && saved.quick.every(c => typeof c === 'string')) this.prefs.quick = saved.quick;
      this.prefs.fingerDraw = !!saved.fingerDraw;
      if (PENS[saved.pen]) this.prefs.pen = saved.pen;
      if (saved.pens && typeof saved.pens === 'object') for (const k in PENS) {
        const v = saved.pens[k];
        if (v && typeof v.color === 'string' && v.size >= MIN_W && v.size <= MAX_W) this.prefs.pens[k] = { color: v.color, size: v.size };
      }
    } catch (e) { /* keep defaults */ }
    this.settings = Object.assign({}, DEFAULT_SETTINGS, await this.loadData());
    if (!BACKGROUNDS[this.settings.background]) this.settings.background = DEFAULT_SETTINGS.background;
    if (!this.settings.looks || typeof this.settings.looks !== 'object') this.settings.looks = {};
    if (!ERASERS[this.settings.eraser]) this.settings.eraser = DEFAULT_SETTINGS.eraser;
    if (!(this.settings.eraserSize >= 4 && this.settings.eraserSize <= 60)) this.settings.eraserSize = DEFAULT_SETTINGS.eraserSize;
    if (typeof this.settings.shapes !== 'boolean') this.settings.shapes = DEFAULT_SETTINGS.shapes;
    if (!(this.settings.shapeHold >= 200 && this.settings.shapeHold <= 1500)) this.settings.shapeHold = DEFAULT_SETTINGS.shapeHold;
    LOOKS = makeLooks(this.settings.looks);
    this.addSettingTab(new ScribbleSettings(this.app, this));
    this.surfaces = new Set(); this.bars = new Set();
    this.focused = null; this.penDown = false; this.penAt = -1e9; this.penDownAt = -1e9; this.penTouch = null;
    this.floatEl = createDiv({ cls: 'scr-bar scr-float' });
    this.floatBar = new Bar(this, this.floatEl, () => this.focused, true);
    this.writing = [   // listeners that exist only while a page or section is being written in
      [window, 'click', e => this.onAnyClick(e), true],
      [window, 'pointerdown', e => this.onAnyPointer(e), { capture: true, passive: true }],
      [window, 'pointermove', e => { if (e.pointerType === 'pen') this.penAt = performance.now(); }, { capture: true, passive: true }],
      [window, 'pointerup', e => this.onAnyPointer(e), { capture: true, passive: true }],
      [window, 'pointercancel', e => this.onAnyPointer(e), { capture: true, passive: true }],
      [window, 'touchstart', e => this.onAnyTouch(e), { capture: true, passive: false }],
      [window, 'touchmove', e => this.onAnyTouch(e), { capture: true, passive: false }],
      [window, 'touchend', e => this.onAnyTouch(e), { capture: true, passive: false }],
      [window, 'touchcancel', e => this.onAnyTouch(e), { capture: true, passive: false }],
      [window, 'resize', () => this.placeFloat(), { passive: true }],
    ];
    this.registerEvent(this.app.workspace.on('active-leaf-change', leaf => {
      const f = this.focused, el = leaf && leaf.view && leaf.view.containerEl;
      if (f && !(el && el.contains(f.root))) this.setFocus(null);
    }));
    this.registerView(VIEW_TYPE, leaf => new ScribbleView(leaf, this));
    this.registerExtensions([EXT], VIEW_TYPE);
    this.registerMarkdownCodeBlockProcessor(EXT, (source, el, ctx) => {
      ctx.addChild(new ScribbleEmbed(el, this, source.trim().split('\n')[0].trim(), ctx.sourcePath));
    });
    this.registerEvent(this.app.workspace.on('css-change', () => { for (const s of this.surfaces) s.redrawAll(); }));
    this.addRibbonIcon('pencil', 'New Scribble page', () => this.newPage());
    // Editor commands show up in Obsidian's "/" slash menu and in the command palette.
    this.addCommand({ id: 'add-new-section', name: 'Add new handwritten section', icon: 'pencil', editorCallback: editor => this.addNewSection(editor) });
    this.addCommand({ id: 'add-existing-section', name: 'Add existing handwritten section', icon: 'files', editorCallback: editor => this.addExistingSection(editor) });
    this.addCommand({ id: 'new-page', name: 'New handwriting page', callback: () => this.newPage() });
  }
  onunload() { this.setFocus(null); this.floatEl.remove(); clearTimeout(this.lookTimer); }
  refreshBars() { for (const b of this.bars) b.refresh(); }
  setLook(kind, key, value) {   // from the settings page; sliders call this many times a second
    if (!LOOK_DEFAULTS[kind]) return;
    const saved = this.settings.looks[kind] || (this.settings.looks[kind] = {});
    if (value === undefined) delete this.settings.looks[kind]; else saved[key] = value;
    LOOKS = makeLooks(this.settings.looks);
    this.refreshBars();
    clearTimeout(this.lookTimer);
    this.lookTimer = setTimeout(() => { for (const s of this.surfaces) s.reindex(); this.saveData(this.settings); }, 200);
  }
  async setBackground(bg) {
    if (!BACKGROUNDS[bg]) return;
    this.settings.background = bg;
    for (const s of this.surfaces) s.setBackground(bg);
    await this.saveData(this.settings);
  }
  closePops() { for (const b of this.bars) if (b.pop) { b.closePop(); b.refresh(); } }
  savePrefs() {
    const p = this.prefs;
    p.pens[p.pen] = { color: p.color, size: p.size };
    try { window.localStorage.setItem(PREFS_KEY, JSON.stringify({ pen: p.pen, pens: p.pens, color: p.color, size: p.size, quick: p.quick, fingerDraw: p.fingerDraw })); } catch (e) { /* private mode etc. */ }
  }
  setPen(k) {   // each pen keeps its own size and colour
    const p = this.prefs; if (!PENS[k]) return;
    p.pens[p.pen] = { color: p.color, size: p.size };
    const v = p.pens[k] || PENS[k].def;
    p.pen = k; p.color = v.color; p.size = v.size; p.tool = 'pen';
    this.savePrefs(); this.refreshBars();
  }

  /* ----- writing mode: one page or section is "in focus" -----
   * While it is: the floating toolbar belongs to it, Obsidian's side drawers do not open by swipe,
   * and touches that arrive while the pen is on (or was just on) the screen are treated as the palm and dropped. */
  setFocus(s) {
    if (s && s.dead) s = null;
    if (this.focused === s) return;
    const was = this.focused;
    if (was) { was.root.removeClass('is-focused'); was.clearSelection(); was.trimTop(); }   // leaving editing: tidy the top
    this.focused = s;
    if (s && !was) { for (const [t, type, fn, o] of this.writing) t.addEventListener(type, fn, o); document.body.dataset.ignoreSwipe = 'true'; }
    if (!s && was) { for (const [t, type, fn, o] of this.writing) t.removeEventListener(type, fn, o); delete document.body.dataset.ignoreSwipe; this.penDown = false; this.penTouch = null; }
    if (s) s.root.addClass('is-focused');
    this.closePops();
    if (s && s.embed) { document.body.appendChild(this.floatEl); this.placeFloat(); } else this.floatEl.remove();
    this.refreshBars();
  }
  placeFloat() {
    const s = this.focused; if (!s || !s.embed) return;
    const host = s.root.closest('.view-content') || s.root, r = host.getBoundingClientRect();
    this.floatEl.style.top = (r.top + 30) + 'px';
    this.floatEl.style.left = (r.left + r.width / 2) + 'px';
  }
  inFocus(t) { const f = this.focused; return !!f && !!t && typeof t.nodeType === 'number' && (f.root.contains(t) || this.floatEl.contains(t)); }
  palm() { return this.penDown || performance.now() - this.penAt < PALM_MS; }
  onAnyClick(e) {   // a deliberate tap outside the section ends writing mode; a palm brushing the note does not
    if (this.inFocus(e.target)) return;
    if (this.palm()) { e.preventDefault(); e.stopPropagation(); return; }
    this.setFocus(null);
  }
  onAnyPointer(e) {
    if (e.pointerType !== 'pen') return;
    const now = performance.now();
    this.penAt = now;
    if (e.type !== 'pointerdown') { this.penDown = false; return; }
    this.penDown = true; this.penDownAt = now; this.penX = e.clientX; this.penY = e.clientY;
    const t = e.target;
    if (!this.inFocus(t) && !(t && t.closest && t.closest('.scr-surface'))) this.setFocus(null);   // pen put down on the note text
  }
  onAnyTouch(e) {
    const ct = e.changedTouches; if (!ct || !ct.length) return;
    if (e.type === 'touchstart') {   // Android reports the pen as a touch as well: recognise it by where and when it landed
      for (const c of ct) {
        if (c.touchType === 'stylus' || (this.penDown && performance.now() - this.penDownAt < 120 && Math.abs(c.clientX - this.penX) < 4 && Math.abs(c.clientY - this.penY) < 4)) this.penTouch = c.identifier;
      }
    }
    let isPen = false;
    for (const c of ct) if (c.identifier === this.penTouch) isPen = true;
    if (isPen) { if (e.type === 'touchend' || e.type === 'touchcancel') this.penTouch = null; return; }
    if (!this.palm()) return;
    const t = e.target;
    if (t && (this.floatEl.contains(t) || (t.closest && t.closest('.scr-bar, .scr-sel-menu')))) return;   // toolbar and selection-menu taps always work
    if (e.cancelable) e.preventDefault();                   // no scrolling, no cursor jump, no keyboard from the palm
    e.stopPropagation();
  }
  async createFile(prefix) {
    if (!this.app.vault.getAbstractFileByPath(FOLDER)) await this.app.vault.createFolder(FOLDER);
    const clean = (prefix || '').replace(/[\\/:*?"<>|#^[\]]/g, ' ').replace(/\s+/g, ' ').trim().slice(0, 60);
    const stamp = window.moment().format('YYYY-MM-DD HHmmss');
    // Never create a 0-byte file: an empty new file did not reach the other devices through Drive sync.
    return this.app.vault.create(FOLDER + '/' + (clean ? clean + ' ' : '') + stamp + '.' + EXT, JSON.stringify({ v: 1, w: PAGE_W, strokes: [] }));
  }
  async newPage() {
    const file = await this.createFile('');
    await this.app.workspace.getLeaf(true).openFile(file);
  }
  insertBlock(editor, path) {
    const cur = editor.getCursor(), line = editor.getLine(cur.line);
    const before = line.slice(0, cur.ch).trim() ? '\n\n' : (cur.line > 0 && editor.getLine(cur.line - 1).trim() ? '\n' : '');
    const after = line.slice(cur.ch).trim() ? '\n\n' : '\n';
    const text = before + '```' + EXT + '\n' + path + '\n```\n' + after;
    editor.replaceRange(text, cur);
    editor.setCursor({ line: cur.line + text.split('\n').length - 1, ch: 0 });   // leave the block so it renders straight away
  }
  async addNewSection(editor) {
    const note = this.app.workspace.getActiveFile();
    const file = await this.createFile(note ? note.basename : '');
    this.insertBlock(editor, file.path);
  }
  addExistingSection(editor) {
    const files = this.app.vault.getFiles().filter(f => f.extension === EXT).sort((a, b) => b.stat.mtime - a.stat.mtime);
    if (!files.length) { new Notice('No handwritten sections yet. Use "Add new handwritten section" first.'); return; }
    new PickScribble(this.app, files, f => this.insertBlock(editor, f.path)).open();
  }
};
module.exports.__test = { cutStroke, paintStroke, drawPreview, LOOK_DEFAULTS, makeLooks, getLooks: () => LOOKS, penWidth, BACKGROUNDS, ScribbleSettings, Surface, ScribbleView, ScribbleEmbed, parseDoc };
