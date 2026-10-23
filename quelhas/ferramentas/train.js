'use strict';
// Treina a avaliação (regressão logística ou MLP pequena) com Adam.
//   node train.js dados.jsonl [mais.jsonl] --hid 16 --ep 30 --lr 0.003 --min 60 --max 100 --out w.json --wm 0.5
const fs = require('fs');
const { extrair, transpor, NF } = require(process.env.FEATS || './feats.js');
const args = process.argv.slice(2);
const get = (k, d) => { const i = args.indexOf(k); return i >= 0 && i + 1 < args.length ? args[i + 1] : d; };
const files = args.filter((a, i) => !a.startsWith('--') && (i === 0 || !args[i - 1].startsWith('--')));
const HID = +get('--hid', 0), EP = +get('--ep', 30), LR = +get('--lr', 0.003), MINL = +get('--min', 0), MAXL = +get('--max', 100);
const OUT = get('--out', 'w.json'), WM = +get('--wm', 0.5), L2 = +get('--l2', 1e-5), SEED = +get('--seed', 1);
function mulberry32(a) { return function () { a |= 0; a = a + 0x6D2B79F5 | 0; let t = Math.imul(a ^ a >>> 15, 1 | a); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; }; }
const rng = mulberry32(SEED);
// carregar
const Xs = [], Ys = [], Ws = [], Ls = [], Ts = [], Gs = [];
const seen = new Map();
for (const f of files) for (const line of fs.readFileSync(f, 'utf8').split('\n')) {
  if (!line) continue;
  const d = JSON.parse(line);
  if (d.live < MINL || d.live > MAXL) continue;
  if (d.tipo === 'r') continue;
  const R = d.o === 'V' ? d.rows : transpor(d.rows);
  const key = R.join(',');
  if (seen.has(key)) continue;           // posição repetida (mesma vista canónica)
  seen.set(key, 1);
  Xs.push(extrair(R)); Ys.push(d.y); Ws.push(d.tipo === 'x' ? 1 : WM); Ls.push(d.live); Ts.push(d.tipo); Gs.push(f + ':' + d.g);
}
const N = Xs.length;
// partição por jogo
const isTest = new Uint8Array(N);
const gt = new Map();
for (let i = 0; i < N; i++) { if (!gt.has(Gs[i])) gt.set(Gs[i], rng() < 0.1); isTest[i] = gt.get(Gs[i]) ? 1 : 0; }
console.log(`posições: ${N} (teste ${isTest.reduce((a, b) => a + b, 0)}), NF=${NF}, HID=${HID}`);
// normalização simples (desvio padrão por característica)
const mu = new Float64Array(NF), sd = new Float64Array(NF);
for (const x of Xs) for (let j = 0; j < NF; j++) { mu[j] += x[j]; sd[j] += x[j] * x[j]; }
for (let j = 0; j < NF; j++) { mu[j] /= N; sd[j] = Math.sqrt(Math.max(1e-6, sd[j] / N - mu[j] * mu[j])); if (j === 0) { mu[j] = 0; sd[j] = 1; } }
for (const x of Xs) for (let j = 0; j < NF; j++) x[j] = (x[j] - mu[j]) / sd[j];
// parâmetros
const nIn = NF;
const P = [];
let W1, b1, W2, b2;
if (HID > 0) {
  W1 = new Float64Array(HID * nIn); b1 = new Float64Array(HID); W2 = new Float64Array(HID); b2 = new Float64Array(1);
  for (let i = 0; i < W1.length; i++) W1[i] = (rng() * 2 - 1) * Math.sqrt(3 / nIn);
  for (let i = 0; i < HID; i++) W2[i] = (rng() * 2 - 1) * Math.sqrt(3 / HID);
  P.push(W1, b1, W2, b2);
} else { W2 = new Float64Array(nIn); b2 = new Float64Array(1); P.push(W2, b2); }
const M = P.map(p => new Float64Array(p.length)), V = P.map(p => new Float64Array(p.length)), G = P.map(p => new Float64Array(p.length));
const hbuf = new Float64Array(Math.max(1, HID));
function forward(x) {
  if (HID > 0) {
    let z = b2[0];
    for (let h = 0; h < HID; h++) {
      let a = b1[h]; const o = h * nIn;
      for (let j = 0; j < nIn; j++) a += W1[o + j] * x[j];
      const r = a > 0 ? a : 0.01 * a; hbuf[h] = r; z += W2[h] * r;
    }
    return z;
  }
  let z = b2[0]; for (let j = 0; j < nIn; j++) z += W2[j] * x[j]; return z;
}
function backward(x, gz) {
  if (HID > 0) {
    G[3][0] += gz;
    for (let h = 0; h < HID; h++) {
      G[2][h] += gz * hbuf[h];
      const gh = gz * W2[h] * (hbuf[h] > 0 ? 1 : 0.01);
      G[1][h] += gh; const o = h * nIn;
      for (let j = 0; j < nIn; j++) G[0][o + j] += gh * x[j];
    }
  } else { G[1][0] += gz; for (let j = 0; j < nIn; j++) G[0][j] += gz * x[j]; }
}
const sig = z => 1 / (1 + Math.exp(-z));
function avaliarConj(test) {
  const buckets = {};
  for (let i = 0; i < N; i++) {
    if (isTest[i] !== test) continue;
    const p = sig(forward(Xs[i])), y = Ys[i];
    const b = (Ts[i] === 'x' ? 'x' : 'm') + (Math.floor(Ls[i] / 5) * 5);
    const B = buckets[b] || (buckets[b] = { n: 0, ll: 0, ac: 0 });
    B.n++; B.ll += -(y ? Math.log(p + 1e-9) : Math.log(1 - p + 1e-9)); B.ac += ((p > 0.5) === (y === 1)) ? 1 : 0;
  }
  return buckets;
}
const idx = []; for (let i = 0; i < N; i++) if (!isTest[i]) idx.push(i);
const BS = 64; let step = 0;
for (let ep = 1; ep <= EP; ep++) {
  for (let i = idx.length - 1; i > 0; i--) { const j = Math.floor(rng() * (i + 1)); const t = idx[i]; idx[i] = idx[j]; idx[j] = t; }
  let tl = 0, tw = 0;
  const lr = LR * (ep > EP * 0.7 ? 0.3 : 1);
  for (let s = 0; s < idx.length; s += BS) {
    for (const g of G) g.fill(0);
    const e = Math.min(idx.length, s + BS);
    for (let k = s; k < e; k++) {
      const i = idx[k], z = forward(Xs[i]), p = sig(z), y = Ys[i], w = Ws[i];
      tl += -w * (y ? Math.log(p + 1e-9) : Math.log(1 - p + 1e-9)); tw += w;
      backward(Xs[i], w * (p - y) / (e - s));
    }
    step++;
    const b1c = 1 - Math.pow(0.9, step), b2c = 1 - Math.pow(0.999, step);
    for (let q = 0; q < P.length; q++) {
      const p = P[q], g = G[q], m = M[q], v = V[q];
      for (let j = 0; j < p.length; j++) {
        const gg = g[j] + L2 * p[j];
        m[j] = 0.9 * m[j] + 0.1 * gg; v[j] = 0.999 * v[j] + 0.001 * gg * gg;
        p[j] -= lr * (m[j] / b1c) / (Math.sqrt(v[j] / b2c) + 1e-8);
      }
    }
  }
  if (ep % 5 === 0 || ep === EP) {
    const B = avaliarConj(1);
    const keys = Object.keys(B).sort();
    let tot = { n: 0, ll: 0, ac: 0 }; for (const k of keys) { tot.n += B[k].n; tot.ll += B[k].ll; tot.ac += B[k].ac; }
    console.log(`ep ${ep} treino ll ${(tl / tw).toFixed(4)} | teste ll ${(tot.ll / tot.n).toFixed(4)} ac ${(100 * tot.ac / tot.n).toFixed(1)}%  ` +
      keys.map(k => `${k}:${(100 * B[k].ac / B[k].n).toFixed(0)}%/${B[k].n}`).join(' '));
  }
}
fs.writeFileSync(OUT, JSON.stringify({ HID, nIn, mu: Array.from(mu), sd: Array.from(sd), P: P.map(p => Array.from(p)) }));
console.log('gravado', OUT);
