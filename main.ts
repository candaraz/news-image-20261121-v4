// THE WORLD IN ONE DAY — Saturday 21 November 2026.
// A one-day newspaper front page, drawn entirely in code: a real serif face
// (Liberation Serif, embedded as a font file) is parsed and rasterised here,
// every picture is drawn from shapes, and the page is written as a PNG.
// Node 22 standard library only. Deterministic: no clock, no randomness.
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { deflateSync } from 'node:zlib';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

const HERE = dirname(fileURLToPath(import.meta.url));
const W = 1024, H = 1024;

// ---------------------------------------------------------------- fonts
// A TrueType face: offset table, cmap format 4, loca/glyf outlines, hmtx
// advances and the format-0 kern table. Outlines are quadratic Beziers;
// they are flattened and filled with a non-zero-winding scanline at 3x
// supersampling, then cached per (face, size, code point).
type Font = {
  buf: Buffer;
  upem: number; locFmt: number; numGlyphs: number; nH: number;
  head: number; hhea: number; hmtx: number; loca: number; glyf: number;
  endO: number; startO: number; deltaO: number; rangeO: number; segCount: number;
  kern: Map<string, number>;
};

function loadFont(path: string): Font {
  const buf = readFileSync(path);
  const u16 = (o: number) => buf.readUInt16BE(o);
  const i16 = (o: number) => buf.readInt16BE(o);
  const u32 = (o: number) => buf.readUInt32BE(o);
  const tables: Record<string, number> = {};
  const nT = u16(4);
  for (let i = 0; i < nT; i++) {
    const o = 12 + i * 16;
    tables[buf.toString('ascii', o, o + 4)] = u32(o + 8);
  }
  const head = tables.head, hhea = tables.hhea, hmtx = tables.hmtx;
  const upem = u16(head + 18), locFmt = i16(head + 50);
  const numGlyphs = u16(tables.maxp + 4), nH = u16(hhea + 34);
  // cmap: prefer a (3,1) format-4 subtable.
  const cmap = tables.cmap; let f4 = -1;
  for (let i = 0; i < u16(cmap + 2); i++) {
    const o = cmap + 4 + i * 8;
    if (u16(o) === 3 && u16(o + 2) === 1) { f4 = cmap + u32(o + 4); break; }
  }
  if (f4 < 0) throw new Error('no format-4 cmap in ' + path);
  const segCount = u16(f4 + 6) / 2;
  const endO = f4 + 14, startO = endO + segCount * 2 + 2;
  const deltaO = startO + segCount * 2, rangeO = deltaO + segCount * 2;
  // kern format 0, if present.
  const kern = new Map<string, number>();
  if (tables.kern !== undefined) {
    const k = tables.kern, nSub = u16(k + 2);
    let p = k + 4;
    for (let s = 0; s < nSub; s++) {
      const len = u16(p + 2), cov = u16(p + 4);
      if ((cov >> 8) === 0) { // format 0
        const nP = u16(p + 6);
        for (let j = 0; j < nP; j++) {
          const q = p + 14 + j * 6;
          kern.set(u16(q) + ',' + u16(q + 2), i16(q + 4));
        }
      }
      p += len;
    }
  }
  return {
    buf, upem, locFmt, numGlyphs, nH, head, hhea, hmtx,
    loca: tables.loca, glyf: tables.glyf,
    endO, startO, deltaO, rangeO, segCount, kern,
  };
}

function glyphId(f: Font, cp: number): number {
  const { buf, endO, startO, deltaO, rangeO, segCount } = f;
  for (let s = 0; s < segCount; s++) {
    const end = buf.readUInt16BE(endO + s * 2), start = buf.readUInt16BE(startO + s * 2);
    if (cp >= start && cp <= end) {
      const d = buf.readInt16BE(deltaO + s * 2), ro = buf.readUInt16BE(rangeO + s * 2);
      if (ro === 0) return (cp + d) & 0xffff;
      return (buf.readUInt16BE(rangeO + s * 2 + ro + (cp - start) * 2) + d) & 0xffff;
    }
  }
  return 0;
}

function glyphOff(f: Font, g: number): number {
  const { buf, loca, glyf, locFmt } = f;
  return locFmt === 0 ? glyf + buf.readUInt16BE(loca + g * 2) * 2 : glyf + buf.readUInt32BE(loca + g * 4);
}

function advanceOf(f: Font, g: number): number {
  return g < f.nH ? f.buf.readUInt16BE(f.hmtx + g * 4) : f.buf.readUInt16BE(f.hmtx + (f.nH - 1) * 4);
}

// One glyph's contours: arrays of [x, y, onCurve] in font units.
function parseGlyph(f: Font, g: number, depth = 0): number[][][] {
  const { buf } = f;
  const o = glyphOff(f, g), o2 = glyphOff(f, g + 1);
  if (o2 <= o) return [];
  const nC = buf.readInt16BE(o);
  if (nC >= 0) {
    const endPts: number[] = [];
    for (let i = 0; i < nC; i++) endPts.push(buf.readUInt16BE(o + 10 + i * 2));
    let p = o + 10 + nC * 2;
    p += 2 + buf.readUInt16BE(p); // skip instructions
    const nPts = endPts.length ? endPts[endPts.length - 1] + 1 : 0;
    const flags: number[] = [];
    while (flags.length < nPts) {
      const fl = buf[p++];
      flags.push(fl);
      if (fl & 8) { const r = buf[p++]; for (let k = 0; k < r; k++) flags.push(fl); }
    }
    const xs: number[] = []; let x = 0;
    for (let i = 0; i < nPts; i++) {
      const fl = flags[i];
      if (fl & 2) { const d = buf[p++]; x += (fl & 16) ? d : -d; }
      else if (!(fl & 16)) { x += buf.readInt16BE(p); p += 2; }
      xs.push(x);
    }
    const ys: number[] = []; let y = 0;
    for (let i = 0; i < nPts; i++) {
      const fl = flags[i];
      if (fl & 4) { const d = buf[p++]; y += (fl & 32) ? d : -d; }
      else if (!(fl & 32)) { y += buf.readInt16BE(p); p += 2; }
      ys.push(y);
    }
    const out: number[][][] = []; let s = 0;
    for (const e of endPts) {
      const pts: number[][] = [];
      for (let i = s; i <= e; i++) pts.push([xs[i], ys[i], (flags[i] & 1) === 1 ? 1 : 0]);
      out.push(pts); s = e + 1;
    }
    return out;
  }
  // Composite glyph.
  let p = o + 10; const out: number[][][] = [];
  for (;;) {
    const fl = buf.readUInt16BE(p), gi = buf.readUInt16BE(p + 2); p += 4;
    let dx = 0, dy = 0, sx = 1, sy = 1;
    if (fl & 1) { dx = buf.readInt16BE(p); dy = buf.readInt16BE(p + 2); p += 4; }
    else { dx = buf[p]; dy = buf[p + 1]; p += 2; }
    if (!(fl & 2)) { dx = 0; dy = 0; } // point matching: not used by these faces
    if (fl & 8) { sx = sy = buf.readInt16BE(p) / 16384; p += 2; }
    else if (fl & 64) { sx = buf.readInt16BE(p) / 16384; sy = buf.readInt16BE(p + 2) / 16384; p += 4; }
    else if (fl & 128) { p += 8; } // 2x2 matrix: treated as identity
    if (depth < 4) for (const c of parseGlyph(f, gi, depth + 1))
      out.push(c.map(([cx, cy, on]) => [Math.round(cx * sx + dx), Math.round(cy * sy + dy), on]));
    if (!(fl & 32)) break;
  }
  return out;
}

// Flatten one contour's quadratics into a polygon (font units).
function flattenContour(pts: number[][]): number[][] {
  const n = pts.length;
  if (!n) return [];
  const seq: number[][] = [];
  const start = pts.findIndex(p => p[2] === 1);
  if (start < 0) {
    for (let i = 0; i < n; i++) {
      const a = pts[i], b = pts[(i + 1) % n];
      seq.push([(a[0] + b[0]) / 2, (a[1] + b[1]) / 2, 1], a);
    }
  } else for (let i = 0; i < n; i++) seq.push(pts[(start + i) % n]);
  const poly: number[][] = [[seq[0][0], seq[0][1]]];
  let cur = seq[0];
  for (let i = 1; i <= seq.length; i++) {
    const p = seq[i % seq.length];
    if (p[2] === 1) { poly.push([p[0], p[1]]); cur = p; continue; }
    const nxt = seq[(i + 1) % seq.length];
    const end: number[] = nxt[2] === 1 ? [nxt[0], nxt[1]] : [(p[0] + nxt[0]) / 2, (p[1] + nxt[1]) / 2];
    for (let t = 1; t <= 8; t++) {
      const u = t / 8, w = 1 - u;
      poly.push([w * w * cur[0] + 2 * w * u * p[0] + u * u * end[0],
                 w * w * cur[1] + 2 * w * u * p[1] + u * u * end[1]]);
    }
    if (nxt[2] === 1) { cur = nxt; i++; } else cur = [end[0], end[1], 1];
  }
  return poly;
}

type GlyphImg = { w: number; h: number; ox: number; oy: number; adv: number; data: Uint8Array };
const glyphCache = new Map<string, GlyphImg>();
const SS = 3; // supersampling factor for anti-aliasing

function rasterGlyph(f: Font, face: number, cp: number, size: number, oblique: boolean): GlyphImg {
  const key = face + ':' + size + ':' + cp + ':' + (oblique ? 1 : 0);
  const hit = glyphCache.get(key);
  if (hit) return hit;
  const gid = glyphId(f, cp);
  const scale = size / f.upem;
  const shear = oblique ? 0.21 : 0;
  const polys = parseGlyph(f, gid).map(c => flattenContour(c).map(([x, y]) => [(x + shear * y) * scale, -y * scale]));
  let minX = 1e9, maxX = -1e9, minY = 1e9, maxY = -1e9;
  for (const poly of polys) for (const [x, y] of poly) {
    if (x < minX) minX = x; if (x > maxX) maxX = x;
    if (y < minY) minY = y; if (y > maxY) maxY = y;
  }
  const adv = advanceOf(f, gid) * scale;
  if (!polys.length || maxX <= minX || maxY <= minY) {
    const g: GlyphImg = { w: 0, h: 0, ox: 0, oy: 0, adv, data: new Uint8Array(0) };
    glyphCache.set(key, g); return g;
  }
  const pad = 1;
  const ox = Math.floor(minX) - pad, oy = Math.floor(minY) - pad;
  const w = Math.ceil(maxX) - ox + pad, h = Math.ceil(maxY) - oy + pad;
  const sw = w * SS, sh = h * SS;
  const edges: number[][] = [];
  for (const poly of polys) for (let i = 0; i < poly.length; i++) {
    const a = poly[i], b = poly[(i + 1) % poly.length];
    const X1 = (a[0] - ox) * SS, Y1 = (a[1] - oy) * SS;
    const X2 = (b[0] - ox) * SS, Y2 = (b[1] - oy) * SS;
    if (Y1 !== Y2) edges.push([X1, Y1, X2, Y2, Y2 > Y1 ? 1 : -1]);
  }
  const cov = new Uint8Array(sw * sh);
  for (let y = 0; y < sh; y++) {
    const yc = y + 0.5, xs: number[][] = [];
    for (const e of edges)
      if (yc >= Math.min(e[1], e[3]) && yc < Math.max(e[1], e[3]))
        // Clamp the crossing: a nearly-horizontal edge can put the
        // intersection far outside the bitmap, and an unclamped fill
        // loop over it spins forever.
        xs.push([Math.max(-1, Math.min(sw + 1, e[0] + (yc - e[1]) / (e[3] - e[1]) * (e[2] - e[0]))), e[4]]);
    xs.sort((a, b) => a[0] - b[0]);
    let wind = 0, prev = 0;
    for (const [xc, d] of xs) {
      if (wind !== 0)
        for (let px = Math.max(0, Math.floor(prev)); px < Math.min(sw, Math.ceil(xc)); px++) cov[y * sw + px]++;
      wind += d; prev = xc;
    }
  }
  const data = new Uint8Array(w * h);
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
    let c = 0;
    for (let dy = 0; dy < SS; dy++) for (let dx = 0; dx < SS; dx++) c += cov[(y * SS + dy) * sw + x * SS + dx];
    data[y * w + x] = Math.round(255 * c / (SS * SS));
  }
  const g: GlyphImg = { w, h, ox, oy, adv, data };
  glyphCache.set(key, g);
  return g;
}

// Faces: 0 regular, 1 bold.
let FACES: Font[] = [];
function face(i: number): Font { return FACES[i]; }

function textWidth(s: string, fi: number, size: number, oblique = false): number {
  const f = face(fi), scale = size / f.upem;
  let w = 0, prev = -1;
  for (const ch of s) {
    const cp = ch.codePointAt(0)!;
    const gid = glyphId(f, cp);
    if (prev >= 0) w += (f.kern.get(prev + ',' + gid) || 0) * scale;
    w += advanceOf(f, gid) * scale;
    prev = gid;
  }
  return w;
}

// Draw text; (x, baselineY) is the start of the baseline. Returns width drawn.
function drawText(x: number, baselineY: number, s: string, fi: number, size: number,
                  col: number[], oblique = false): number {
  const f = face(fi), scale = size / f.upem;
  let pen = x, prev = -1;
  for (const ch of s) {
    const cp = ch.codePointAt(0)!;
    const gid = glyphId(f, cp);
    if (prev >= 0) pen += (f.kern.get(prev + ',' + gid) || 0) * scale;
    const g = rasterGlyph(f, fi, cp, size, oblique);
    if (g.w > 0) blit(Math.round(pen) + g.ox, Math.round(baselineY) + g.oy, g, col);
    pen += g.adv;
    prev = gid;
  }
  return pen - x;
}

// Greedy word wrap; returns lines that each fit maxW.
function wrap(s: string, fi: number, size: number, maxW: number, oblique = false): string[] {
  const words = s.split(' ');
  const lines: string[] = [];
  let cur = '';
  for (const w of words) {
    const t = cur ? cur + ' ' + w : w;
    if (textWidth(t, fi, size, oblique) <= maxW || !cur) cur = t;
    else { lines.push(cur); cur = w; }
  }
  if (cur) lines.push(cur);
  return lines;
}

function drawPara(x: number, y: number, s: string, fi: number, size: number, maxW: number,
                  col: number[], lh: number, oblique = false): number {
  const lines = wrap(s, fi, size, maxW, oblique);
  lines.forEach((ln, i) => drawText(x, y + (i + 1) * size * 0.82 + i * (lh - size * 0.82), ln, fi, size, col, oblique));
  return lines.length * lh;
}

// ---------------------------------------------------------------- canvas
const img = new Uint8Array(W * H * 3);
const PAPER: number[] = [250, 246, 236];
const INK: number[] = [26, 26, 26];
const RED: number[] = [178, 34, 34];
const DRED: number[] = [140, 22, 22];
const GREY: number[] = [110, 108, 100];
const LGREY: number[] = [226, 222, 210];

function fillPaper() { for (let i = 0; i < W * H; i++) { img[i * 3] = PAPER[0]; img[i * 3 + 1] = PAPER[1]; img[i * 3 + 2] = PAPER[2]; } }

function setPx(x: number, y: number, c: number[]) {
  if (x < 0 || y < 0 || x >= W || y >= H) return;
  const o = (y * W + x) * 3;
  img[o] = c[0]; img[o + 1] = c[1]; img[o + 2] = c[2];
}

function blit(x0: number, y0: number, g: GlyphImg, col: number[]) {
  for (let y = 0; y < g.h; y++) {
    const yy = y0 + y;
    if (yy < 0 || yy >= H) continue;
    for (let x = 0; x < g.w; x++) {
      const a = g.data[y * g.w + x];
      if (!a) continue;
      const xx = x0 + x;
      if (xx < 0 || xx >= W) continue;
      const o = (yy * W + xx) * 3, ia = 255 - a;
      img[o] = (a * col[0] + ia * img[o]) / 255 | 0;
      img[o + 1] = (a * col[1] + ia * img[o + 1]) / 255 | 0;
      img[o + 2] = (a * col[2] + ia * img[o + 2]) / 255 | 0;
    }
  }
}

function fillRect(x: number, y: number, w: number, h: number, c: number[]) {
  const x0 = Math.max(0, Math.round(x)), y0 = Math.max(0, Math.round(y));
  const x1 = Math.min(W, Math.round(x + w)), y1 = Math.min(H, Math.round(y + h));
  for (let yy = y0; yy < y1; yy++) for (let xx = x0; xx < x1; xx++) setPx(xx, yy, c);
}

function hline(x1: number, x2: number, y: number, c: number[], t = 1) {
  fillRect(Math.min(x1, x2), y - Math.floor(t / 2), Math.abs(x2 - x1), t, c);
}

function vline(x: number, y1: number, y2: number, c: number[], t = 1) {
  fillRect(x - Math.floor(t / 2), Math.min(y1, y2), t, Math.abs(y2 - y1), c);
}

// Straight line, drawn by walking the longer axis between the rounded
// endpoints. (A Bresenham over float endpoints can step past the rounded
// target and never land on it, so it spins forever.)
function line(x1: number, y1: number, x2: number, y2: number, c: number[], t = 1) {
  const X1 = Math.round(x1), Y1 = Math.round(y1), X2 = Math.round(x2), Y2 = Math.round(y2);
  const steps = Math.max(Math.abs(X2 - X1), Math.abs(Y2 - Y1));
  const r = Math.floor(t / 2);
  if (steps === 0) {
    for (let a = -r; a <= r; a++) for (let b = -r; b <= r; b++) setPx(X1 + a, Y1 + b, c);
    return;
  }
  for (let i = 0; i <= steps; i++) {
    const x = Math.round(X1 + i * (X2 - X1) / steps);
    const y = Math.round(Y1 + i * (Y2 - Y1) / steps);
    for (let a = -r; a <= r; a++) for (let b = -r; b <= r; b++) setPx(x + a, y + b, c);
  }
}

// Quadratic Bezier as a polyline.
function quad(x1: number, y1: number, cx: number, cy: number, x2: number, y2: number, c: number[], t = 1) {
  let px = x1, py = y1;
  for (let i = 1; i <= 24; i++) {
    const u = i / 24, w = 1 - u;
    const x = w * w * x1 + 2 * w * u * cx + u * u * x2;
    const y = w * w * y1 + 2 * w * u * cy + u * u * y2;
    line(px, py, x, y, c, t); px = x; py = y;
  }
}

function fillCircle(cx: number, cy: number, r: number, c: number[]) {
  for (let y = Math.floor(cy - r); y <= Math.ceil(cy + r); y++) {
    const dx = Math.sqrt(Math.max(0, r * r - (y - cy) * (y - cy)));
    for (let x = Math.floor(cx - dx); x <= Math.ceil(cx + dx); x++) setPx(x, y, c);
  }
}

function circle(cx: number, cy: number, r: number, c: number[], t = 1) {
  for (let a = 0; a < 360; a += 2) {
    const rad = a * Math.PI / 180;
    setPx(Math.round(cx + r * Math.cos(rad)), Math.round(cy + r * Math.sin(rad)), c);
    if (t > 1) { setPx(Math.round(cx + (r - 1) * Math.cos(rad)), Math.round(cy + (r - 1) * Math.sin(rad)), c); }
  }
}

// Non-zero winding fill for a polygon.
function fillPoly(pts: number[][], c: number[]) {
  let minY = 1e9, maxY = -1e9;
  for (const p of pts) { if (p[1] < minY) minY = p[1]; if (p[1] > maxY) maxY = p[1]; }
  for (let y = Math.max(0, Math.floor(minY)); y <= Math.min(H - 1, Math.ceil(maxY)); y++) {
    const yc = y + 0.5, xs: number[][] = [];
    for (let i = 0; i < pts.length; i++) {
      const a = pts[i], b = pts[(i + 1) % pts.length];
      if (a[1] === b[1]) continue;
      if (yc >= Math.min(a[1], b[1]) && yc < Math.max(a[1], b[1]))
        xs.push([a[0] + (yc - a[1]) / (b[1] - a[1]) * (b[0] - a[0]), b[1] > a[1] ? 1 : -1]);
    }
    xs.sort((p, q) => p[0] - q[0]);
    let wind = 0, prev = 0;
    for (const [xc, d] of xs) {
      if (wind !== 0)
        for (let xx = Math.max(0, Math.floor(prev)); xx < Math.min(W, Math.ceil(xc)); xx++) setPx(xx, y, c);
      wind += d; prev = xc;
    }
  }
}

// An 8-point starburst, for missile bursts and blasts.
function starburst(cx: number, cy: number, r: number, c: number[]) {
  const pts: number[][] = [];
  for (let i = 0; i < 16; i++) {
    const a = i * Math.PI / 8 - Math.PI / 2;
    const rr = i % 2 === 0 ? r : r * 0.38;
    pts.push([cx + rr * Math.cos(a), cy + rr * Math.sin(a)]);
  }
  fillPoly(pts, c);
  fillCircle(cx, cy, Math.max(2, r * 0.3), [255, 255, 255]);
}

// ---------------------------------------------------------------- PNG
function crc32(buf: Buffer): number {
  let tab = (crc32 as any).tab as Int32Array | undefined;
  if (!tab) {
    tab = new Int32Array(256);
    for (let n = 0; n < 256; n++) {
      let v = n;
      for (let k = 0; k < 8; k++) v = v & 1 ? 0xedb88320 ^ (v >>> 1) : v >>> 1;
      tab[n] = v;
    }
    (crc32 as any).tab = tab;
  }
  let c = 0xffffffff;
  for (const b of buf) c = tab[(c ^ b) & 255] ^ (c >>> 8);
  return (c ^ 0xffffffff) >>> 0;
}

function pngChunk(type: string, data: Buffer): Buffer {
  const len = Buffer.alloc(4); len.writeUInt32BE(data.length);
  const crc = Buffer.alloc(4); crc.writeUInt32BE(crc32(Buffer.concat([Buffer.from(type, 'ascii'), data])));
  return Buffer.concat([len, Buffer.from(type, 'ascii'), data, crc]);
}

function writePNG(path: string) {
  const raw = Buffer.alloc(H * (W * 3 + 1));
  for (let y = 0; y < H; y++) {
    raw[y * (W * 3 + 1)] = 0;
    raw.set(img.subarray(y * W * 3, (y + 1) * W * 3), y * (W * 3 + 1) + 1);
  }
  const ihdr = Buffer.alloc(13);
  ihdr.writeUInt32BE(W, 0); ihdr.writeUInt32BE(H, 4);
  ihdr[8] = 8; ihdr[9] = 2; // 8-bit RGB
  const png = Buffer.concat([
    Buffer.from([137, 80, 78, 71, 13, 10, 26, 10]),
    pngChunk('IHDR', ihdr),
    pngChunk('IDAT', deflateSync(raw, { level: 9 })),
    pngChunk('IEND', Buffer.alloc(0)),
  ]);
  writeFileSync(path, png);
}

// ---------------------------------------------------------------- pictures
// Every picture on the page is drawn from shapes. Coordinates are absolute
// pixels inside the box each function is given; nothing here is random, so
// the page is byte-identical on every run.

const SKY: number[] = [13, 27, 62];
const OCEAN: number[] = [127, 179, 213];
const LAND: number[] = [93, 168, 93];
const TAN: number[] = [214, 193, 150];
const MAPSEA: number[] = [220, 228, 232];

function drawGlobe(cx: number, cy: number, r: number) {
  fillCircle(cx, cy, r, OCEAN);
  circle(cx, cy, r, [70, 110, 140], 2);
  // Continents, as rough blobs: Americas, Africa, Eurasia.
  fillPoly([[cx - r * 0.72, cy - r * 0.55], [cx - r * 0.42, cy - r * 0.62], [cx - r * 0.28, cy - r * 0.30],
            [cx - r * 0.38, cy + r * 0.05], [cx - r * 0.55, cy + r * 0.42], [cx - r * 0.78, cy + r * 0.18]], LAND);
  fillPoly([[cx + r * 0.05, cy - r * 0.42], [cx + r * 0.30, cy - r * 0.45], [cx + r * 0.38, cy - r * 0.05],
            [cx + r * 0.22, cy + r * 0.35], [cx + r * 0.02, cy + r * 0.10]], LAND);
  fillPoly([[cx + r * 0.35, cy - r * 0.70], [cx + r * 0.75, cy - r * 0.68], [cx + r * 0.85, cy - r * 0.30],
            [cx + r * 0.62, cy - r * 0.18], [cx + r * 0.45, cy - r * 0.42]], LAND);
  // Graticule.
  hline(cx - r, cx + r, cy, [255, 255, 255], 1);
  for (const f of [-0.5, 0.5]) {
    const yy = cy + f * r;
    const dx = Math.sqrt(Math.max(0, r * r - (yy - cy) * (yy - cy)));
    hline(cx - dx, cx + dx, yy, [255, 255, 255], 1);
  }
  for (let a = 0; a < 180; a += 4) {
    const rad = a * Math.PI / 180;
    setPx(Math.round(cx + r * 0.55 * Math.cos(rad)), Math.round(cy + r * Math.sin(rad)), [255, 255, 255]);
    setPx(Math.round(cx - r * 0.55 * Math.cos(rad)), Math.round(cy + r * Math.sin(rad)), [255, 255, 255]);
  }
}

function drawThermometer(x: number, y: number, h: number) {
  const w = 16, cx = x + w / 2;
  fillRect(cx - 2, y + 6, 4, h - 22, [255, 255, 255]);
  fillRect(cx - 2, y + 6 + (h - 22) * 0.28, 4, (h - 22) * 0.72, [200, 40, 40]);
  fillCircle(cx, y + h - 10, 9, [200, 40, 40]);
  fillCircle(cx, y + h - 10, 5, [230, 80, 80]);
  // Tick marks.
  for (let i = 0; i <= 4; i++) hline(cx + 5, cx + 9, y + 8 + i * ((h - 26) / 4), INK, 1);
}

function drawClock(cx: number, cy: number, r: number) {
  fillCircle(cx, cy, r, [255, 255, 255]);
  circle(cx, cy, r, INK, 2);
  for (let i = 0; i < 12; i++) {
    const a = i * Math.PI / 6;
    line(cx + (r - 3) * Math.sin(a), cy - (r - 3) * Math.cos(a), cx + (r - 6) * Math.sin(a), cy - (r - 6) * Math.cos(a), INK, 1);
  }
  // Hands at five to twelve: talks past their deadline.
  line(cx, cy, cx - r * 0.55, cy - r * 0.62, INK, 3);
  line(cx, cy, cx + r * 0.42, cy - r * 0.72, INK, 3);
  fillCircle(cx, cy, 2, INK);
}

// Night skyline over Riyadh: black towers with lit windows, three curved
// missile arcs rising to bursts. The arcs are what make the panel read as
// missiles over a city, not a chart.
function drawSkyline(x: number, y: number, w: number, h: number) {
  fillRect(x, y, w, h, SKY);
  // Stars.
  const stars: number[][] = [[0.08, 0.12], [0.22, 0.06], [0.35, 0.16], [0.52, 0.08], [0.66, 0.14], [0.78, 0.05], [0.88, 0.18], [0.95, 0.10], [0.45, 0.20], [0.60, 0.24]];
  for (const [fx, fy] of stars) fillRect(x + fx * w, y + fy * h, 2, 2, [255, 255, 255]);
  // Moon.
  fillCircle(x + w * 0.90, y + h * 0.20, 9, [240, 238, 220]);
  fillCircle(x + w * 0.90 + 4, y + h * 0.20 - 2, 8, SKY);
  // Towers: [x fraction, width fraction, height fraction].
  const towers: number[][] = [
    [0.00, 0.11, 0.52], [0.11, 0.09, 0.70], [0.20, 0.12, 0.44], [0.32, 0.10, 0.62],
    [0.42, 0.11, 0.38], [0.53, 0.09, 0.66], [0.62, 0.12, 0.48], [0.74, 0.10, 0.72],
    [0.84, 0.08, 0.55], [0.92, 0.08, 0.42],
  ];
  for (let t = 0; t < towers.length; t++) {
    const [fx, fw, fh] = towers[t];
    const bx = x + fx * w, bw = fw * w, bh = fh * h, by = y + h - bh;
    fillRect(bx, by, bw, bh, [8, 10, 18]);
    // Lit windows: a fixed pattern, denser near the top.
    const cols = Math.max(1, Math.floor(bw / 9)), rows = Math.max(1, Math.floor(bh / 12));
    for (let r = 0; r < rows; r++) for (let c = 0; c < cols; c++) {
      if ((t * 7 + r * 3 + c * 5) % 5 < 2)
        fillRect(bx + 3 + c * 9, by + 5 + r * 12, 4, 5, [255, 214, 110]);
    }
  }
  // Three interceptor arcs, rising from the towers to bursts.
  const arcs: number[][] = [
    [0.16, 0.98, 0.30, 0.28, 0.44, 0.22],
    [0.50, 0.98, 0.55, 0.34, 0.68, 0.30],
    [0.72, 0.98, 0.82, 0.40, 0.90, 0.18],
  ];
  for (const [fx1, fy1, fcx, fcy, fx2, fy2] of arcs) {
    // Dashed arc: draw it in short pieces.
    let px = x + fx1 * w, py = y + fy1 * h;
    for (let i = 1; i <= 24; i++) {
      const u = i / 24, wgt = 1 - u;
      const nx = wgt * wgt * (x + fx1 * w) + 2 * wgt * u * (x + fcx * w) + u * u * (x + fx2 * w);
      const ny = wgt * wgt * (y + fy1 * h) + 2 * wgt * u * (y + fcy * h) + u * u * (y + fy2 * h);
      if (i % 2 === 0) line(px, py, nx, ny, [255, 230, 140], 2);
      px = nx; py = ny;
    }
    starburst(x + fx2 * w, y + fy2 * h, 11, [255, 200, 60]);
  }
  // Ground line.
  fillRect(x, y + h - 3, w, 3, [8, 10, 18]);
}

// Peru: a seismograph band above houses with red roofs.
function drawQuake(x: number, y: number, w: number, h: number) {
  fillRect(x, y, w, h, [238, 230, 210]);
  const bandY = y + 8, bandH = 52;
  fillRect(x + 8, bandY, w - 16, bandH, [255, 255, 255]);
  // Seismogram: a fixed jagged trace, tall in the middle.
  const amps: number[] = [2, 3, 2, 4, 3, 6, 4, 9, 5, 14, 7, 20, 8, 12, 5, 16, 6, 9, 4, 7, 3, 5, 2, 3, 2];
  const n = amps.length, step = (w - 24) / (n - 1), mid = bandY + bandH / 2;
  let px = x + 12, py = mid;
  for (let i = 1; i < n; i++) {
    const nx = x + 12 + i * step;
    const ny = mid + (i % 2 === 0 ? -1 : 1) * amps[i] * 0.9;
    line(px, py, nx, ny, [178, 34, 34], 2);
    px = nx; py = ny;
  }
  hline(x + 8, x + w - 8, mid, [200, 190, 175], 1);
  // Houses with red roofs, on a ridge.
  const houses: number[][] = [
    [0.04, 0.62, 0.16, 0.13], [0.24, 0.58, 0.18, 0.16], [0.46, 0.66, 0.15, 0.12],
    [0.64, 0.60, 0.17, 0.15], [0.84, 0.64, 0.13, 0.11],
  ];
  const baseY = y + h - 8;
  for (const [fx, fy, fw, fh] of houses) {
    const hx = x + fx * w, hw = fw * w, hh = fh * h, hy = y + fy * h;
    fillRect(hx, hy, hw, baseY - hy, [196, 164, 120]);
    fillPoly([[hx - 4, hy], [hx + hw / 2, hy - hh * 0.55], [hx + hw + 4, hy]], [165, 40, 40]);
    fillRect(hx + hw * 0.32, hy + (baseY - hy) * 0.35, hw * 0.18, (baseY - hy) * 0.65, [60, 45, 30]);
    fillRect(hx + hw * 0.62, hy + (baseY - hy) * 0.30, hw * 0.16, (baseY - hy) * 0.28, [70, 80, 95]);
  }
  // A taller block at the right, for scale.
  fillRect(x + w * 0.86, y + h * 0.42, w * 0.10, baseY - (y + h * 0.42), [150, 140, 120]);
  for (let r = 0; r < 3; r++) for (let c = 0; c < 2; c++)
    fillRect(x + w * 0.86 + 4 + c * 12, y + h * 0.46 + r * 12, 6, 7, [240, 230, 200]);
}

// Small line icons for the ten small panels, drawn in a 30x30 box.
function drawIcon(kind: string, x: number, y: number, s: number) {
  const u = s / 30;
  const ink: number[] = [40, 40, 40];
  if (kind === 'bridge') {
    line(x + 2 * u, y + 22 * u, x + 28 * u, y + 22 * u, ink, 2);
    line(x + 2 * u, y + 22 * u, x + 15 * u, y + 6 * u, ink, 2);
    line(x + 28 * u, y + 22 * u, x + 15 * u, y + 6 * u, ink, 2);
    vline(x + 15 * u, y + 6 * u, y + 22 * u, ink, 2);
    line(x + 8 * u, y + 22 * u, x + 15 * u, y + 14 * u, ink, 1);
    line(x + 22 * u, y + 22 * u, x + 15 * u, y + 14 * u, ink, 1);
  } else if (kind === 'drone') {
    fillPoly([[x + 4 * u, y + 14 * u], [x + 12 * u, y + 10 * u], [x + 18 * u, y + 10 * u], [x + 26 * u, y + 14 * u],
              [x + 18 * u, y + 17 * u], [x + 12 * u, y + 17 * u]], [70, 70, 70]);
    line(x + 2 * u, y + 8 * u, x + 10 * u, y + 8 * u, ink, 2);
    line(x + 20 * u, y + 8 * u, x + 28 * u, y + 8 * u, ink, 2);
    fillCircle(x + 6 * u, y + 8 * u, 2, ink); fillCircle(x + 24 * u, y + 8 * u, 2, ink);
    line(x + 15 * u, y + 17 * u, x + 15 * u, y + 24 * u, ink, 1);
  } else if (kind === 'atom') {
    fillCircle(x + 15 * u, y + 15 * u, 3, [178, 34, 34]);
    for (let k = 0; k < 3; k++) {
      const a = k * Math.PI / 3;
      for (let t = 0; t <= 24; t++) {
        const th = t / 24 * Math.PI * 2;
        setPx(Math.round(x + 15 * u + 11 * u * Math.cos(th) * Math.cos(a) - 5 * u * Math.sin(th) * Math.sin(a)),
              Math.round(y + 15 * u + 11 * u * Math.cos(th) * Math.sin(a) + 5 * u * Math.sin(th) * Math.cos(a)), ink);
      }
    }
  } else if (kind === 'tax') {
    fillRect(x + 4 * u, y + 8 * u, 10 * u, 14 * u, [60, 90, 140]);
    fillRect(x + 16 * u, y + 4 * u, 10 * u, 18 * u, [90, 120, 170]);
    for (let r = 0; r < 3; r++) { fillRect(x + 6 * u, y + 11 * u + r * 4 * u, 6 * u, 1, [255, 255, 255]); fillRect(x + 18 * u, y + 7 * u + r * 4 * u, 6 * u, 1, [255, 255, 255]); }
    drawText(x + 8 * u, y + 30 * u, '%', 1, 11, [178, 34, 34]);
  } else if (kind === 'flags') {
    // China (red, stars) and Japan (white, red disc) side by side.
    fillRect(x + 2 * u, y + 6 * u, 12 * u, 9 * u, [222, 41, 16]);
    starburst(x + 6 * u, y + 10 * u, 2, [255, 222, 0]);
    fillRect(x + 16 * u, y + 6 * u, 12 * u, 9 * u, [255, 255, 255]);
    fillCircle(x + 22 * u, y + 10 * u, 3, [188, 0, 45]);
    fillRect(x + 2 * u, y + 17 * u, 12 * u, 9 * u, [0, 47, 108]);
    fillRect(x + 16 * u, y + 17 * u, 12 * u, 9 * u, [220, 30, 30]);
    drawText(x + 5 * u, y + 25 * u, '*', 1, 10, [255, 255, 255]);
  } else if (kind === 'plane') {
    fillPoly([[x + 2 * u, y + 15 * u], [x + 10 * u, y + 12 * u], [x + 24 * u, y + 12 * u], [x + 28 * u, y + 15 * u],
              [x + 24 * u, y + 17 * u], [x + 10 * u, y + 17 * u]], [90, 110, 140]);
    fillPoly([[x + 12 * u, y + 12 * u], [x + 16 * u, y + 5 * u], [x + 18 * u, y + 12 * u]], [90, 110, 140]);
    fillPoly([[x + 20 * u, y + 17 * u], [x + 23 * u, y + 23 * u], [x + 25 * u, y + 17 * u]], [90, 110, 140]);
    line(x + 2 * u, y + 24 * u, x + 28 * u, y + 24 * u, [120, 120, 120], 1);
  } else if (kind === 'chat') {
    fillPoly([[x + 3 * u, y + 6 * u], [x + 17 * u, y + 6 * u], [x + 17 * u, y + 16 * u], [x + 9 * u, y + 16 * u],
              [x + 6 * u, y + 21 * u], [x + 6 * u, y + 16 * u], [x + 3 * u, y + 16 * u]], [178, 34, 34]);
    fillPoly([[x + 13 * u, y + 12 * u], [x + 27 * u, y + 12 * u], [x + 27 * u, y + 22 * u], [x + 21 * u, y + 22 * u],
              [x + 24 * u, y + 27 * u], [x + 18 * u, y + 22 * u], [x + 13 * u, y + 22 * u]], [40, 90, 140]);
  } else if (kind === 'bitcoin') {
    fillCircle(x + 15 * u, y + 15 * u, 12, [247, 147, 26]);
    drawText(x + 10 * u, y + 21 * u, 'B', 1, 17, [255, 255, 255]);
    vline(x + 13 * u, y + 6 * u, y + 24 * u, [255, 255, 255], 1);
    vline(x + 17 * u, y + 6 * u, y + 24 * u, [255, 255, 255], 1);
    line(x + 4 * u, y + 26 * u, x + 10 * u, y + 22 * u, [178, 34, 34], 2);
    line(x + 10 * u, y + 22 * u, x + 16 * u, y + 24 * u, [178, 34, 34], 2);
    line(x + 16 * u, y + 24 * u, x + 26 * u, y + 19 * u, [178, 34, 34], 2);
  } else if (kind === 'car') {
    fillPoly([[x + 3 * u, y + 20 * u], [x + 6 * u, y + 13 * u], [x + 12 * u, y + 11 * u], [x + 20 * u, y + 11 * u],
              [x + 25 * u, y + 14 * u], [x + 27 * u, y + 20 * u]], [200, 30, 30]);
    fillCircle(x + 9 * u, y + 21 * u, 3, INK); fillCircle(x + 21 * u, y + 21 * u, 3, INK);
    fillCircle(x + 9 * u, y + 21 * u, 1, [255, 255, 255]); fillCircle(x + 21 * u, y + 21 * u, 1, [255, 255, 255]);
    // Chequered flag.
    for (let r = 0; r < 3; r++) for (let c = 0; c < 3; c++)
      if ((r + c) % 2 === 0) fillRect(x + 24 * u + c * 2 * u, y + 2 * u + r * 2 * u, 2 * u, 2 * u, INK);
    line(x + 24 * u, y + 2 * u, x + 24 * u, y + 12 * u, INK, 1);
  } else if (kind === 'cricket') {
    // Bat, ball and stumps on a green strip.
    fillRect(x + 2 * u, y + 24 * u, 26 * u, 4 * u, [90, 160, 90]);
    line(x + 8 * u, y + 24 * u, x + 8 * u, y + 12 * u, [200, 170, 90], 3);
    line(x + 12 * u, y + 24 * u, x + 12 * u, y + 12 * u, [200, 170, 90], 3);
    line(x + 16 * u, y + 24 * u, x + 16 * u, y + 12 * u, [200, 170, 90], 3);
    fillPoly([[x + 20 * u, y + 6 * u], [x + 24 * u, y + 6 * u], [x + 23 * u, y + 18 * u], [x + 19 * u, y + 18 * u]], [190, 160, 110]);
    fillCircle(x + 25 * u, y + 22 * u, 2, [178, 34, 34]);
  }
}

// A simplified world map with numbered pins for the thirteen panel stories.
function drawMap(x: number, y: number, w: number, h: number) {
  fillRect(x, y, w, h, MAPSEA);
  const lon = (lo: number) => x + (lo + 180) / 360 * w;
  const lat = (la: number) => y + (78 - la) / 135 * h;
  const polys: number[][][] = [
    // North America
    [[-168, 66], [-140, 70], [-120, 72], [-95, 80], [-80, 73], [-75, 62], [-65, 60], [-55, 47], [-70, 42], [-75, 35], [-80, 25], [-90, 21], [-97, 16], [-105, 20], [-110, 24], [-117, 33], [-125, 40], [-125, 49], [-135, 58], [-155, 58]],
    // South America
    [[-80, 10], [-77, 4], [-80, -4], [-81, -6], [-77, -12], [-72, -18], [-70, -23], [-70, -30], [-72, -37], [-73, -44], [-70, -52], [-66, -55], [-65, -45], [-58, -38], [-52, -32], [-48, -27], [-41, -22], [-35, -9], [-35, -6], [-43, 0], [-50, 0], [-55, 5], [-62, 9], [-70, 11]],
    // Africa
    [[-17, 15], [-17, 21], [-10, 31], [-5, 35], [10, 37], [20, 32], [32, 31], [35, 28], [37, 22], [39, 18], [43, 12], [48, 11], [51, 10], [46, 5], [41, -2], [40, -10], [36, -18], [32, -26], [28, -33], [20, -35], [17, -29], [14, -22], [12, -12], [13, -5], [9, 4], [-8, 4], [-13, 8]],
    // Eurasia
    [[-10, 36], [-9, 43], [-2, 48], [-4, 50], [0, 51], [3, 53], [8, 57], [10, 59], [18, 56], [21, 55], [24, 58], [28, 60], [30, 62], [40, 68], [55, 68], [68, 73], [80, 73], [100, 77], [120, 73], [140, 72], [160, 70], [178, 65], [170, 60], [162, 56], [158, 52], [150, 59], [142, 55], [140, 50], [135, 44], [130, 42], [127, 40], [122, 38], [120, 35], [122, 31], [118, 25], [110, 21], [105, 10], [103, 8], [100, 8], [97, 15], [94, 17], [89, 22], [86, 20], [80, 15], [77, 8], [75, 10], [72, 20], [66, 25], [58, 25], [52, 28], [48, 30], [44, 29], [40, 25], [36, 20], [34, 28], [30, 36], [27, 37], [23, 36], [20, 40], [16, 40], [12, 44], [8, 44], [3, 43], [0, 40], [-2, 37], [-6, 36], [-9, 37]],
    // Australia
    [[113, -22], [114, -30], [115, -33], [118, -35], [124, -33], [129, -32], [132, -32], [135, -35], [138, -35], [140, -38], [145, -38], [150, -37], [153, -32], [153, -27], [150, -22], [146, -19], [142, -15], [142, -11], [137, -12], [135, -15], [132, -12], [130, -13], [126, -14], [122, -17], [118, -20]],
    // Greenland
    [[-58, 64], [-52, 60], [-45, 60], [-40, 64], [-32, 68], [-25, 70], [-20, 74], [-25, 78], [-35, 80], [-50, 80], [-58, 76], [-60, 72]],
  ];
  for (const poly of polys) fillPoly(poly.map(([lo, la]) => [lon(lo), lat(la)]), TAN);
  // Pins: [story number, lon, lat].
  const pins: number[][] = [
    [1, 32.9, 36.9], [2, 46.7, 24.6], [3, -76, -10.9], [4, 30.5, 50.5], [5, 56.5, 26.5],
    [6, 51.4, 35.7], [7, -77, 38.9], [8, 116.4, 39.9], [9, 125.6, 7.1], [10, 149.1, -35.3],
    [11, -30, 0], [12, -115.1, 36.2], [13, 174.8, -41.3],
  ];
  for (const [n, lo, la] of pins) {
    const px = Math.min(x + w - 10, Math.max(x + 10, lon(lo)));
    const py = Math.min(y + h - 10, Math.max(y + 10, lat(la)));
    fillPoly([[px, py - 8], [px + 8, py], [px, py + 8], [px - 8, py]], [178, 34, 34]);
    const label = String(n);
    const tw = textWidth(label, 1, 10);
    drawText(px - tw / 2, py + 3.5, label, 1, 10, [255, 255, 255]);
  }
}

// ---------------------------------------------------------------- the page
const LABEL_BG: Record<string, number[]> = {
  CONFIRMED: [46, 125, 50], OFFICIAL: [31, 78, 121],
  REPORTED: [178, 106, 0], CLAIM: [102, 102, 102],
};

// A small white-on-colour verification label, right-aligned at (x, y).
function drawLabel(x: number, y: number, text: string) {
  const bg = LABEL_BG[text] || [102, 102, 102];
  const w = textWidth(text, 1, 9) + 8;
  fillRect(x - w, y, w, 12, bg);
  drawText(x - w + 4, y + 9.5, text, 1, 9, [255, 255, 255]);
}

function fitSize(s: string, fi: number, size: number, maxW: number): number {
  let sz = size;
  while (sz > 8 && textWidth(s, fi, sz) > maxW) sz -= 1;
  return sz;
}

// ---- data: the day's 35 stories, as reported on 21 November 2026.
// Heroes carry the three biggest stories; the ten small panels the next ten;
// the list carries the remaining twenty-two. Counts are the winners' own.
type Hero = {
  n: number; place: string; field: string; kicker: string; badge: string;
  headline: string; body: string; source: string; label: string; art: string;
};
type Small = {
  n: number; place: string; field: string; kicker: string; icon: string;
  headline: string; body: string; source: string; label: string;
};

const HEROES: Hero[] = [
  {
    n: 1, place: 'ANTALYA, TÜRKIYE', field: 'CLIMATE', kicker: 'COP31: OVERTIME', badge: 'NO DEAL · DAY 13',
    headline: 'Summit misses its deadline as talks split',
    body: 'COP31 missed its Friday close with no deal, split by a draft with no mention of fossil fuels. A third text is promised for Saturday morning.',
    source: '(AP, AFP, Al Jazeera)', label: 'CONFIRMED', art: 'cop31',
  },
  {
    n: 2, place: 'RIYADH', field: 'WAR', kicker: 'SAUDI: MISSILES', badge: '3 SHOT DOWN',
    headline: 'Three missiles downed over Riyadh',
    body: 'The coalition said three ballistic missiles fired towards Riyadh were destroyed before dawn, the third night of alerts in a row. No damage was reported.',
    source: '(Reuters, AFP, coalition)', label: 'OFFICIAL', art: 'saudi',
  },
  {
    n: 3, place: 'CARHUAMAYO, PERU', field: 'EARTHQUAKE', kicker: 'PERU: QUAKE 6.7', badge: '00:09 UTC · 108 KM DEEP',
    headline: 'Magnitude 6.7 quake shakes central Peru',
    body: 'The deep quake near Carhuamayo was felt in Lima and along the coast. Peru’s institute reported no deaths, no damage and no tsunami risk.',
    source: '(USGS, IGP)', label: 'OFFICIAL', art: 'peru',
  },
];

const SMALLS: Small[] = [
  { n: 4, place: 'KYIV', field: 'WAR', kicker: 'KYIV: WARNING', icon: 'bridge',
    headline: 'Zelensky: Crimea bridge “will not stay”', body: 'He warns of more double-tap strikes.',
    source: '(NBC)', label: 'REPORTED' },
  { n: 5, place: 'STRAIT OF HORMUZ', field: 'WAR', kicker: 'HORMUZ: DRONE', icon: 'drone',
    headline: 'Iran says it downed a US drone', body: 'No confirmation yet from Washington.',
    source: '(IRIB)', label: 'CLAIM' },
  { n: 6, place: 'TEHRAN', field: 'DIPLOMACY', kicker: 'IRAN: URANIUM', icon: 'atom',
    headline: 'Iran: uranium stock stays at home', body: 'Minister still seeks a “fair solution”.',
    source: '(Times of Israel)', label: 'OFFICIAL' },
  { n: 7, place: 'WASHINGTON', field: 'TECHNOLOGY', kicker: 'TRUMP: AI TAX', icon: 'tax',
    headline: 'Trump vows tax on data centres abroad', body: '“Tremendous” penalty; no details yet.',
    source: '(ABC)', label: 'REPORTED' },
  { n: 8, place: 'BEIJING', field: 'DIPLOMACY', kicker: 'CHINA–JAPAN', icon: 'flags',
    headline: 'China tells Japan to “correct” its Taiwan words', body: 'Tokyo says its stance is unchanged.',
    source: '(Ministry, AFP)', label: 'OFFICIAL' },
  { n: 9, place: 'DAVAO', field: 'AVIATION', kicker: 'DAVAO: 146 SAFE', icon: 'plane',
    headline: 'Jet lands safely after engine fire alert', body: 'Air Niugini 767 diverts after midnight.',
    source: '(Airline, AP)', label: 'OFFICIAL' },
  { n: 10, place: 'CANBERRA', field: 'DIPLOMACY', kicker: 'CANBERRA: AI', icon: 'chat',
    headline: 'Australia and China agree AI talks', body: 'Albanese ends an 11-day trip.',
    source: '(ABC)', label: 'OFFICIAL' },
  { n: 11, place: 'WORLD', field: 'MARKETS', kicker: 'BITCOIN: $58,983', icon: 'bitcoin',
    headline: 'Bitcoin slips below $59,000', body: 'Down 3.9% in 24 hours; ether $1,625.',
    source: '(CoinGecko)', label: 'CONFIRMED' },
  { n: 12, place: 'LAS VEGAS', field: 'FORMULA ONE', kicker: 'RUSSELL: P1', icon: 'car',
    headline: 'Russell fastest in final Vegas practice', body: '1:34.041 in a damp, messy session.',
    source: '(Formula 1)', label: 'OFFICIAL' },
  { n: 13, place: 'WELLINGTON', field: 'CRICKET', kicker: 'RAHUL: 124*', icon: 'cricket',
    headline: 'Rahul century puts India on top', body: 'India 344 for 2 at tea, replying to 368.',
    source: '(AFP)', label: 'OFFICIAL' },
];

// The remaining twenty-two stories, in two columns of eleven.
const MORE: string[] = [
  'Kryvyi Rih: double strike kills 2, injures 42 (Kyiv Indep.)',
  'Copenhagen: Russian attacks expelled in plot (Al Jazeera)',
  'Antalya: EU warns COP31 risks a “fossil summit” (AFP)',
  'Antalya: Panama may block the climate text (Al Jazeera)',
  'Antalya: PLN signs six clean-power deals (Antara)',
  'Yemen: Houthis threaten Jeddah and Red Sea ports (Al Jazeera)',
  'Washington: Vance: Iran strikes were Trump’s call (Reuters)',
  'Washington: lawmaker threatens SpaceX’s funding (CNN)',
  'Texas: execution of man of 70 takes 63 minutes (ABC)',
  'Los Angeles: jury convicts Palisades fire starter (ABC)',
  'Missouri: judge approves $7.25bn Roundup deal (AFP)',
  'Vancouver: Canada rests defence in youth climate trial (AFP)',
  'Pyongyang: Kim tours factories after no Trump meeting (AFP)',
  'Sejong: freight train derails; no one hurt (Korea Herald)',
  'Taipei: budget and a cash payout are passed (Taipei Times)',
  'Bangkok: six-point plan on arsenic in two rivers (The Nation)',
  'New Delhi: Pakistani minister joins SCO forum in India (Dawn)',
  'Eastern India: rain alerts as Akvan remnants move inland (ETV)',
  'Myanmar: rights groups urge sanctions after court ruling (AP)',
  'Port Louis: rating agency talks to 15 states (Al Jazeera)',
  'Melbourne: Cummins keeps the Australian captaincy (ABC)',
  'Las Vegas: Verstappen sent to stewards (Autosport)',
];

const STATS: [string, string][] = [
  ['13', 'Day 13 of a COP31 summit planned to close on day 12'],
  ['3', 'missiles shot down over Riyadh'],
  ['6.7', 'magnitude of the Peru quake'],
  ['146', 'people safe after the Davao landing'],
  ['$58,983', 'bitcoin early Saturday, down 3.9% in a day'],
  ['124*', 'K L Rahul’s score at tea, Wellington'],
];

const REGIONS: [string, number, number[]][] = [
  ['Europe 4', 108, [31, 78, 121]], ['Asia 10', 266, [178, 34, 34]], ['Middle East 5', 132, [178, 106, 0]],
  ['Africa 1', 56, [46, 125, 50]], ['Americas 11', 282, [103, 78, 140]], ['Oceania 3', 92, [0, 128, 128]],
  ['Global 1', 56, [110, 108, 100]],
];

function drawHero(x: number, y: number, w: number, h: number, s: Hero) {
  // Picture.
  if (s.art === 'cop31') {
    fillRect(x, y, w, 104, [222, 235, 240]);
    drawGlobe(x + 58, y + 50, 40);
    drawThermometer(x + 138, y + 8, 86);
    drawText(x + 128, y + 10, '+1.5°C', 1, 12, RED);
    drawText(x + 118, y + 102, 'LIMIT AT RISK', 1, 9, INK);
    drawClock(x + 262, y + 50, 38);
    drawText(x + 240, y + 102, 'DAY 13', 1, 11, INK);
  } else if (s.art === 'saudi') {
    drawSkyline(x, y, w, 104);
  } else {
    drawQuake(x, y, w, 104);
  }
  // Kicker bar with badge.
  fillRect(x, y + 104, w, 22, RED);
  drawText(x + 8, y + 104 + 16, s.kicker, 1, 14, [255, 255, 255]);
  const bw = textWidth(s.badge, 1, 10) + 12;
  fillRect(x + w - bw - 6, y + 108, bw, 14, DRED);
  drawText(x + w - bw, y + 104 + 16, s.badge, 1, 10, [255, 255, 255]);
  // Location, headline, body, source + label.
  drawText(x + 2, y + 142, s.n + ' · ' + s.place + ' · ' + s.field, 1, 10.5, RED);
  const hl = wrap(s.headline, 1, 19, w - 4);
  hl.forEach((ln, i) => drawText(x + 2, y + 146 + (i + 1) * 19, ln, 1, 19, INK));
  const bodyY = y + 146 + hl.length * 19 + 4;
  drawPara(x + 2, bodyY, s.body, 0, 12, w - 4, INK, 15);
  drawText(x + 2, y + h - 4, s.source, 0, 10, GREY, true);
  drawLabel(x + w - 2, y + h - 16, s.label);
}

function drawSmall(x: number, y: number, w: number, h: number, s: Small) {
  // Kicker bar: white icon chip, then title.
  fillRect(x, y, w, 20, RED);
  fillRect(x + 2, y + 2, 16, 16, [255, 255, 255]);
  drawIcon(s.icon, x + 2.5, y + 2.5, 15);
  drawText(x + 22, y + 15, s.kicker, 1, 11.5, [255, 255, 255]);
  drawText(x + 2, y + 33, s.n + ' · ' + s.place + ' · ' + s.field, 1, 9.5, RED);
  const hl = wrap(s.headline, 1, 13.5, w - 4);
  hl.forEach((ln, i) => drawText(x + 2, y + 37 + (i + 1) * 13.5, ln, 1, 13.5, INK));
  const bodyY = y + 37 + hl.length * 13.5 + 3;
  drawPara(x + 2, bodyY, s.body, 0, 11, w - 4, INK, 13.5);
  drawText(x + 2, y + h - 3, s.source, 0, 9.5, GREY, true);
  drawLabel(x + w - 2, y + h - 15, s.label);
}

function main() {
  FACES = [loadFont(join(HERE, 'fonts', 'LiberationSerif-Regular.ttf')),
           loadFont(join(HERE, 'fonts', 'LiberationSerif-Bold.ttf'))];
  fillPaper();
  const MX = 16, CW = 992;

  // Top band.
  fillRect(0, 0, W, 26, RED);
  drawText(16, 18, 'THE WORLD IN ONE DAY', 1, 13, [255, 255, 255]);
  const bandR = '35 STORIES · 7 REGIONS · EVERY ONE DATED SATURDAY 21 NOVEMBER 2026';
  drawText(W - 16 - textWidth(bandR, 1, 11), 18, bandR, 1, 11, [255, 255, 255]);

  // Masthead and standfirst.
  const mast = 'Saturday 21 November 2026';
  const msz = fitSize(mast, 1, 62, CW);
  const mtw = textWidth(mast, 1, msz);
  drawText((W - mtw) / 2, 84, mast, 1, msz, INK);
  const sub = 'COP31 talks run into overtime · three missiles over Riyadh · a quake shakes Peru';
  const stw = textWidth(sub, 0, 16.5, true);
  drawText((W - stw) / 2, 110, sub, 0, 16.5, INK, true);
  hline(MX, MX + CW, 120, INK, 2);

  // Stats row: six boxes with a big red number and a two-line caption.
  const sw = CW / 6;
  STATS.forEach(([num, cap], i) => {
    const bx = MX + i * sw;
    if (i > 0) vline(bx, 128, 182, LGREY, 1);
    const nsz = fitSize(num, 1, 30, sw - 12);
    const ntw = textWidth(num, 1, nsz);
    drawText(bx + (sw - ntw) / 2, 158, num, 1, nsz, RED);
    const lines = wrap(cap, 0, 10.5, sw - 14);
    lines.forEach((ln, j) => {
      const ltw = textWidth(ln, 0, 10.5);
      drawText(bx + (sw - ltw) / 2, 172 + j * 12, ln, 0, 10.5, INK);
    });
  });
  hline(MX, MX + CW, 184, LGREY, 1);

  // Region bar.
  let rx = MX;
  for (const [label, w, col] of REGIONS) {
    fillRect(rx, 188, w - 2, 18, col);
    const ltw = textWidth(label, 1, 10);
    drawText(rx + (w - 2 - ltw) / 2, 201, label, 1, 10, [255, 255, 255]);
    rx += w;
  }

  // Heroes.
  const hw = (CW - 16) / 3;
  HEROES.forEach((s, i) => drawHero(MX + i * (hw + 8), 212, hw, 252, s));

  // Two rows of five small panels.
  const pw = (CW - 24) / 5;
  SMALLS.slice(0, 5).forEach((s, i) => drawSmall(MX + i * (pw + 6), 472, pw, 104, s));
  SMALLS.slice(5).forEach((s, i) => drawSmall(MX + i * (pw + 6), 582, pw, 104, s));

  // Bottom: map on the left, the twenty-two more stories on the right.
  drawText(MX, 708, 'WHERE IT HAPPENED', 1, 13, INK);
  drawMap(MX, 714, 320, 224);
  drawText(MX, 946, 'Each number is the story with that number on this page.', 0, 10, GREY, true);
  const lx = MX + 328, lw = CW - 328;
  drawText(lx, 708, 'ALSO ON SATURDAY 21 NOVEMBER — 22 MORE STORIES', 1, 13, INK);
  const colW = (lw - 12) / 2;
  MORE.forEach((row, i) => {
    const col = i < 11 ? 0 : 1;
    const r = i % 11;
    const x = lx + col * (colW + 12), y = 708 + r * 21;
    const num = String(i + 14);
    drawText(x, y + 11, num, 1, 10.5, RED);
    const nw = textWidth(num + ' ', 1, 10.5);
    let sz = 10.5;
    while (sz > 9 && textWidth(row, 0, sz) > colW - nw - 2) sz -= 0.5;
    drawText(x + nw, y + 11, row, 0, sz, INK);
  });

  // Date check: what was left out, and why.
  const dc = 'DATE CHECK — Left out as Friday 20 November’s news: Wall Street’s fall into a correction, the Russian barrage that hit Kyiv’s bridges, the missile that landed in Poland, the UK–EU deal and Cyclone Akvan’s landfall. Older still: Voyager 1’s light-day (18 Nov). Not confirmed when drawn: BepiColombo in Mercury orbit, a final COP31 text.';
  fillRect(MX, 950, CW, 40, PAPER);
  for (let k = 0; k < 2; k++) { hline(MX, MX + CW, 950 + k, RED, 1); hline(MX, MX + CW, 989 - k, RED, 1); }
  vline(MX, 950, 990, RED, 1); vline(MX + CW, 950, 990, RED, 1);
  const dcLines = wrap(dc, 0, 10.5, CW - 16);
  dcLines.forEach((ln, i) => drawText(MX + 8, 964 + i * 13.5, ln, 0, 10.5, INK));

  // Footer: the promise, and how each story was checked.
  const f1 = 'Every story here happened, or was first reported, on Saturday 21 November 2026.';
  const f1w = textWidth(f1, 0, 10.5);
  drawText((W - f1w) / 2, 1002, f1, 0, 10.5, INK);
  const f2 = 'Sources named beside each story · Original drawings · HOW WE CHECKED: CONFIRMED = 2+ outlets · OFFICIAL = on the record · REPORTED = one outlet · CLAIM = one side’s account';
  const f2w = textWidth(f2, 0, 9.5);
  drawText((W - f2w) / 2, 1016, f2, 0, 9.5, GREY);

  const outDir = process.env.MAKEFUN_OUTPUT_DIR || 'out';
  mkdirSync(outDir, { recursive: true });
  writePNG(join(outDir, 'entry.png'));
}

main();
