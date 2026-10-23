'use strict';
// Solver exato por regiões (o mesmo de bot_novo.js), como módulo para as ferramentas de dados.
//   const E = require('./solver_regioes.js'); E.resolver(tab, 'V', limiteMs) -> true se quem tem a vez ganha
const FULL = 0x3FF;
const WIN = 1000000, MATE_TH = WIN - 1000, INF = 2000000000;
const EXACT = 1, LOWER = 2, UPPER = 3;
const ABORT = { abort: true };

// ---------- Tabelas por máscara de 10 bits ----------
const SEGS = new Array(1024), RUNS = new Array(1024), SPANS = new Array(1024);
const NSEG = new Uint8Array(1024), NRUN = new Uint8Array(1024);
const POPC = new Uint8Array(1024), CTZ = new Int8Array(1024), REVW = new Int16Array(11 * 1024);
const DRUN = new Int8Array(16384);      // (x<<4)|c -> variação do nº de runs de x ao tirar a casa c
(function () {
  for (let m = 0; m < 1024; m++) {
    let p = 0; for (let b = 0; b < 10; b++) if ((m >> b) & 1) p++;
    POPC[m] = p;
    CTZ[m] = m ? 31 - Math.clz32(m & -m) : -1;
    const segs = [], runs = [], spans = [];
    let i = 0;
    while (i < 10) {
      if (!((m >> i) & 1)) { i++; continue; }
      let j = i; while (j < 10 && ((m >> j) & 1)) j++;
      const L = j - i;
      spans.push(((1 << L) - 1) << i);
      if (L >= 2) {
        runs.push(((1 << L) - 1) << i);
        for (let s = i; s <= j - 2; s++) for (let l = 2; s + l <= j; l++) segs.push((s << 4) | l);
      }
      i = j;
    }
    SEGS[m] = Int16Array.from(segs); NSEG[m] = segs.length;
    RUNS[m] = Int16Array.from(runs); NRUN[m] = runs.length; SPANS[m] = Int16Array.from(spans);
    for (let w = 1; w <= 10; w++) {
      let r = 0; for (let b = 0; b < w; b++) if ((m >> b) & 1) r |= 1 << (w - 1 - b);
      REVW[w * 1024 + m] = r;
    }
  }
  for (let x = 0; x < 1024; x++) for (let c = 0; c < 10; c++) DRUN[(x << 4) | c] = NRUN[x & ~(1 << c)] - NRUN[x];
})();

// ---------- Números aleatórios para hashing (splitmix32: não linear, lanes independentes) ----------
let zs = 0x2545F491;
function zr() {
  zs = zs + 0x9E3779B9 | 0; let z = zs;
  z = Math.imul(z ^ (z >>> 16), 0x85EBCA6B); z = Math.imul(z ^ (z >>> 13), 0xC2B2AE35); return (z ^ (z >>> 16)) | 0;
}
const ZA = new Int32Array(100), ZB = new Int32Array(100);
for (let i = 0; i < 100; i++) ZA[i] = zr();
for (let i = 0; i < 100; i++) ZB[i] = zr();
const SA = zr(), SB = zr();
const ZC1 = new Int32Array(10), ZC2 = new Int32Array(10);
for (let i = 0; i < 10; i++) { ZC1[i] = zr() | 1; ZC2[i] = zr() | 1; }
function fmix(h) { h ^= h >>> 16; h = Math.imul(h, 0x85EBCA6B); h ^= h >>> 13; h = Math.imul(h, 0xC2B2AE35); h ^= h >>> 16; return h; }

// =====================================================================================
// Solver exato por regiões
// =====================================================================================
const POOL = 1 << 16;
const CR = new Int16Array(POOL * 10), CC = new Int16Array(POOL * 10);   // máscaras por linha e por coluna
const CB = new Int8Array(POOL * 4), CH = new Int32Array(POOL * 4);      // r0 r1 c0 c1; hash V (2 lanes), hash H (2 lanes)
let poolTop = 0;
const TMP = new Int32Array(12);
let hA = 0, hB = 0;
// hash canónico de uma forma (linhas TMP[0..h-1] já deslocadas, largura w): mínimo das 4 variantes
function shapeHash(h, w) {
  const base = w * 1024;
  let a0 = h * 16 + w, a1 = a0, a2 = a0, a3 = a0;
  for (let i = 0; i < h; i++) {
    const m = TMP[i], mr = TMP[h - 1 - i];
    a0 = Math.imul(a0 ^ m, 0x01000193) + 0x632BE5AB | 0;
    a1 = Math.imul(a1 ^ mr, 0x01000193) + 0x632BE5AB | 0;
    a2 = Math.imul(a2 ^ REVW[base + m], 0x01000193) + 0x632BE5AB | 0;
    a3 = Math.imul(a3 ^ REVW[base + mr], 0x01000193) + 0x632BE5AB | 0;
  }
  a0 = fmix(a0); a1 = fmix(a1); a2 = fmix(a2); a3 = fmix(a3);
  let best = a0, vb = 0;
  if ((a1 >>> 0) < (best >>> 0)) { best = a1; vb = 1; }
  if ((a2 >>> 0) < (best >>> 0)) { best = a2; vb = 2; }
  if ((a3 >>> 0) < (best >>> 0)) { best = a3; vb = 3; }
  let b = Math.imul(h * 16 + w, 0x9E3779B1) ^ 0x7F4A7C15;   // 2.ª lane: cadeia independente sobre a variante escolhida
  for (let i = 0; i < h; i++) {
    let m = (vb & 1) ? TMP[h - 1 - i] : TMP[i];
    if (vb & 2) m = REVW[base + m];
    b = Math.imul(b + m + 0x165667B1, 0x27D4EB2F); b ^= b >>> 15;
  }
  b = Math.imul(b ^ (b >>> 13), 0x5BD1E995); b ^= b >>> 16;
  hA = best; hB = b;
}
const MAXP = 100, MAXC = 48;
const LIST = new Int32Array(MAXP * MAXC), NL = new Int32Array(MAXP);
const CNTV = new Int8Array(MAXP * 5), CNTH = new Int8Array(MAXP * 5);   // runs exclusivas de V e de H por classe
const S = new Int32Array(12), LV = new Int32Array(12), X = new Int32Array(12);
// decompõe as casas S[1..10] (linhas; S[0] = S[11] = 0) e acrescenta regiões/contadores ao nível p
function decompor(p) {
  for (let r = 1; r <= 10; r++) { const f = S[r]; LV[r] = f & ((S[r - 1] | S[r + 1]) | ((f << 1) | (f >> 1))); }
  const cv = p * 5;
  for (;;) {
    let r0 = 1; while (r0 <= 10 && !LV[r0]) r0++;
    if (r0 > 10) break;
    for (let r = 0; r <= 11; r++) X[r] = 0;
    X[r0] = SPANS[LV[r0]][0];
    let lo = r0, hi = r0, ch = true;
    while (ch) {
      ch = false;
      for (let r = lo; r <= 10; r++) {
        const lc = LV[r]; const x = X[r] | ((X[r - 1] | X[r + 1]) & lc);
        if (x === X[r]) { if (r > hi) break; continue; }
        const sp = SPANS[lc]; let y = 0; for (let j = 0; j < sp.length; j++) if (sp[j] & x) y |= sp[j];
        X[r] = y; ch = true; if (r > hi) hi = r;
      }
      for (let r = hi; r >= 1; r--) {
        const lc = LV[r]; const x = X[r] | ((X[r - 1] | X[r + 1]) & lc);
        if (x === X[r]) { if (r < lo) break; continue; }
        const sp = SPANS[lc]; let y = 0; for (let j = 0; j < sp.length; j++) if (sp[j] & x) y |= sp[j];
        X[r] = y; ch = true; if (r < lo) lo = r;
      }
    }
    for (let r = lo; r <= hi; r++) LV[r] &= ~X[r];
    let or = 0; for (let r = lo; r <= hi; r++) or |= X[r];
    if (lo === hi) { CNTH[cv + (POPC[or] >> 1) - 1]++; continue; }                 // run horizontal exclusiva
    if ((or & (or - 1)) === 0) { CNTV[cv + ((hi - lo + 1) >> 1) - 1]++; continue; } // run vertical exclusiva
    const id = poolTop++, b10 = id * 10, c0 = CTZ[or & -or], c1 = 31 - Math.clz32(or);
    for (let i = 0; i < 10; i++) { CR[b10 + i] = 0; CC[b10 + i] = 0; }
    for (let r = lo; r <= hi; r++) {
      let x = X[r]; CR[b10 + r - 1] = x;
      while (x) { const bb = x & -x; x ^= bb; CC[b10 + CTZ[bb]] |= 1 << (r - 1); }
    }
    CB[id * 4] = lo - 1; CB[id * 4 + 1] = hi - 1; CB[id * 4 + 2] = c0; CB[id * 4 + 3] = c1;
    const h = hi - lo + 1, w = c1 - c0 + 1;
    for (let i = 0; i < h; i++) TMP[i] = X[lo + i] >> c0;
    shapeHash(h, w); CH[id * 4] = hA; CH[id * 4 + 1] = hB;
    for (let i = 0; i < w; i++) TMP[i] = CC[b10 + c0 + i] >> (lo - 1);
    shapeHash(w, h); CH[id * 4 + 2] = hA; CH[id * 4 + 3] = hB;
    LIST[p * MAXC + NL[p]++] = id;
  }
}
function carregarRows(rows) {   // nível 0 a partir das máscaras de linhas livres
  poolTop = 0; NL[0] = 0;
  for (let i = 0; i < 5; i++) { CNTV[i] = 0; CNTH[i] = 0; }
  S[0] = 0; S[11] = 0;
  for (let r = 0; r < 10; r++) S[r + 1] = rows[r];
  decompor(0);
}
const SBITS = 23, SMASK = (1 << SBITS) - 1;
// baldes de 2 entradas; em caso de conflito substitui-se a de menor trabalho (log2 dos nós da subárvore)
const sKey = new Int32Array(1 << SBITS), sVal = new Uint8Array(1 << SBITS), sWork = new Uint8Array(1 << SBITS);   // valor: 6 bits extra da chave | 1 ganha / 2 perde
let sNodes = 0, sNodeLim = Infinity;
const SBUF = []; for (let i = 0; i < MAXP; i++) SBUF.push(new Int32Array(1024));
const ABS = 63;      // índice de região especial: jogada abstrata numa run exclusiva
const PF = new Int32Array(12);
// jogada do solver: idxRegião<<12 | linha<<8 | início<<4 | comprimento  (abstratas: ABS<<12 | classe<<8 | encurtar)
function fazer(p, side, mv) {
  const q = p + 1, li = mv >>> 12, base = p * MAXC, nb = q * MAXC, cvp = p * 5, cvq = q * 5;
  for (let i = 0; i < 5; i++) { CNTV[cvq + i] = CNTV[cvp + i]; CNTH[cvq + i] = CNTH[cvp + i]; }
  if (li === ABS) {
    const n = NL[p]; for (let i = 0; i < n; i++) LIST[nb + i] = LIST[base + i]; NL[q] = n;
    const t = (mv >> 8) & 15, A = side === 0 ? CNTV : CNTH;
    A[cvq + t]--; if (mv & 1) A[cvq + t - 1]++;
    return;
  }
  let n = 0; const np = NL[p];
  for (let i = 0; i < np; i++) if (i !== li) LIST[nb + n++] = LIST[base + i];
  NL[q] = n;
  const id = LIST[base + li], b10 = id * 10, line = (mv >> 8) & 15, s = (mv >> 4) & 15, l = mv & 15;
  S[0] = 0; S[11] = 0;
  for (let r = 0; r < 10; r++) S[r + 1] = CR[b10 + r];
  if (side === 0) { const bit = ~(1 << line); for (let r = s; r < s + l; r++) S[r + 1] &= bit; }
  else S[line + 1] &= ~(((1 << l) - 1) << s);
  decompor(q);
}
// gera e pontua as jogadas (partir runs do adversário +, criar runs minhas -); regiões repetidas só uma vez
function gerarSolver(p, side, buf) {
  const base = p * MAXC, n = NL[p], cv = p * 5, ME = side === 0 ? CNTV : CNTH, ho = side === 0 ? 0 : 2;
  let m = 0;
  for (let i = 0; i < n; i++) {
    const id = LIST[base + i], b10 = id * 10, li = i << 12;
    let dup = false;
    for (let j = 0; j < i; j++) { const jd = LIST[base + j]; if (CH[jd * 4 + ho] === CH[id * 4 + ho] && CH[jd * 4 + ho + 1] === CH[id * 4 + ho + 1]) { dup = true; break; } }
    if (dup) continue;
    const vert = side === 0, a0 = vert ? CB[id * 4 + 2] : CB[id * 4], a1 = vert ? CB[id * 4 + 3] : CB[id * 4 + 1];
    const MY = vert ? CC : CR, OPM = vert ? CR : CC;
    for (let c = a0; c <= a1; c++) {
      const rm = RUNS[MY[b10 + c]];
      for (let j = 0; j < rm.length; j++) {
        const run = rm[j], s0 = CTZ[run], Lr = POPC[run];
        for (let k = 0; k < Lr; k++) PF[k + 1] = PF[k] + DRUN[(OPM[b10 + s0 + k] << 4) | c];
        for (let a = 0; a <= Lr - 2; a++) for (let l = 2; a + l <= Lr; l++) {
          const my = (a >= 2 ? 1 : 0) + (Lr - a - l >= 2 ? 1 : 0) - 1, op = PF[a + l] - PF[a];
          buf[m++] = ((((op * 2 - my * 3) * 16 + l) + 1024) << 18) | li | (c << 8) | ((s0 + a) << 4) | l;
        }
      }
    }
  }
  let tc = -1, ts = -1;
  for (let t = 0; t < 5; t++) if (ME[cv + t] > 0) { if (tc < 0) tc = t; if (t >= 1 && ts < 0) ts = t; }
  if (tc >= 0) buf[m++] = ((3 * 16 + 1024) << 18) | (ABS << 12) | (tc << 8);
  if (ts >= 0) buf[m++] = (1024 << 18) | (ABS << 12) | (ts << 8) | 1;
  return m;
}
// true se quem tem a vez (side: 0 = V, 1 = H) ganha no nível p
function resolve(p, side) {
  if ((++sNodes & 1023) === 0 && (sNodes >= sNodeLim || Date.now() >= deadline)) throw ABORT;
  const base = p * MAXC, n = NL[p], cv = p * 5;
  const ME = side === 0 ? CNTV : CNTH, OP = side === 0 ? CNTH : CNTV;
  if (n === 0) return ME[cv] + ME[cv + 1] + ME[cv + 2] + ME[cv + 3] + ME[cv + 4] <= OP[cv] + OP[cv + 1] + OP[cv + 2] + OP[cv + 3] + OP[cv + 4];
  let k1 = 0, k2 = 0;
  const ho = side === 0 ? 0 : 2;
  for (let i = 0; i < n; i++) { const id = LIST[base + i]; k1 = k1 + CH[id * 4 + ho] | 0; k2 = k2 + CH[id * 4 + ho + 1] | 0; }
  for (let i = 0; i < 5; i++) {
    const a = ME[cv + i], b = OP[cv + i];
    k1 = k1 + Math.imul(a, ZC1[i]) + Math.imul(b, ZC1[5 + i]) | 0;
    k2 = k2 + Math.imul(a, ZC2[i]) + Math.imul(b, ZC2[5 + i]) | 0;
  }
  const e0 = k1 & (SMASK - 1), tag = (k1 >>> 26) << 2;
  let ev = sVal[e0];
  if (ev !== 0 && sKey[e0] === k2 && (ev & 0xFC) === tag) return (ev & 3) === 1;
  ev = sVal[e0 + 1];
  if (ev !== 0 && sKey[e0 + 1] === k2 && (ev & 0xFC) === tag) return (ev & 3) === 1;
  const n0 = sNodes;
  const buf = SBUF[p], m = gerarSolver(p, side, buf);
  buf.subarray(0, m).sort();
  const save = poolTop;
  let win = false;
  for (let i = m - 1; i >= 0; i--) {
    fazer(p, side, buf[i] & 0x3FFFF);
    const w = resolve(p + 1, side ^ 1);
    poolTop = save;
    if (!w) { win = true; break; }
  }
  // lugar e0 guarda a entrada mais trabalhosa; e0+1 é de substituição sempre
  const wk = 32 - Math.clz32(sNodes - n0 + 1);
  let ej;
  if (sKey[e0] === k2 && (sVal[e0] & 0xFC) === tag) ej = e0;
  else if (sKey[e0 + 1] === k2 && (sVal[e0 + 1] & 0xFC) === tag) ej = e0 + 1;
  else ej = wk >= sWork[e0] ? e0 : e0 + 1;
  sKey[ej] = k2; sVal[ej] = tag | (win ? 1 : 2); sWork[ej] = wk;
  return win;
}

let deadline = Infinity;
function resolver(tab, orient, lim) {
  const rows = []; for (let r = 0; r < 10; r++) { let m = 0; for (let c = 0; c < 10; c++) if (!tab[r][c]) m |= 1 << c; rows.push(m); }
  carregarRows(rows); sNodes = 0; sNodeLim = Infinity; deadline = lim === undefined ? Infinity : Date.now() + lim;
  return resolve(0, orient === 'V' ? 0 : 1);
}
module.exports = { resolver, get nodes() { return sNodes; }, limpar() { sVal.fill(0); sWork.fill(0); } };
