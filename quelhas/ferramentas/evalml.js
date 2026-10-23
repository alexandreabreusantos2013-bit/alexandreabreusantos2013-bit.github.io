'use strict';
// Avaliação aprendida rápida (sem alocações). Replica feats.js. R/C = linhas/colunas da vista canónica (quem joga é vertical).
const FULL = 0x3FF;
const RUNS = new Array(1024), POPC = new Uint8Array(1024), CTZ = new Int8Array(1024), NSEG = new Uint8Array(1024);
const SPL = new Uint8Array(1024 * 1024 / 1024); // não usado
(function () {
  for (let m = 0; m < 1024; m++) {
    let p = 0; for (let b = 0; b < 10; b++) if ((m >> b) & 1) p++;
    POPC[m] = p; CTZ[m] = m ? 31 - Math.clz32(m & -m) : -1;
    const runs = []; let i = 0, ns = 0;
    while (i < 10) {
      if (!((m >> i) & 1)) { i++; continue; }
      let j = i; while (j < 10 && ((m >> j) & 1)) j++;
      const L = j - i; if (L >= 2) { runs.push(((1 << L) - 1) << i); ns += (L - 1) * L / 2; }
      i = j;
    }
    RUNS[m] = Int16Array.from(runs); NSEG[m] = ns;
  }
})();
const PAT = new Int16Array(256); let NPAT = 0;
(function () {
  const flipV = [5, 6, 7, 3, 4, 0, 1, 2], flipH = [2, 1, 0, 4, 3, 7, 6, 5];
  const ap = (m, perm) => { let r = 0; for (let i = 0; i < 8; i++) if ((m >> i) & 1) r |= 1 << perm[i]; return r; };
  const cls = new Map();
  for (let m = 0; m < 256; m++) {
    const vs = [m, ap(m, flipV), ap(m, flipH), ap(ap(m, flipV), flipH)];
    const k = Math.min(...vs);
    if (!cls.has(k)) cls.set(k, NPAT++);
    PAT[m] = cls.get(k);
  }
})();
const NG = 64, NF = NG + NPAT;
// máscara "partível": para uma run (máscara) e máscara de casas disputadas, há casa disputada a >=2 das pontas?
const Rp = new Int32Array(12), Cp = new Int32Array(12), G = new Float64Array(NG);
const exV = new Int32Array(5), exH = new Int32Array(5), ctV = new Int32Array(5), ctH = new Int32Array(5);
// preenche G[0..43] e devolve; os padrões são acumulados diretamente em acc (callback de pesos)
function globais(R, C) {
  Rp[0] = 0; Rp[11] = 0; Cp[0] = 0; Cp[11] = 0;
  for (let i = 0; i < 10; i++) { Rp[i + 1] = R[i]; Cp[i + 1] = C[i]; }
  let cont = 0, liveV = 0, liveH = 0, live = 0, privV = 0, privH = 0;
  for (let r = 1; r <= 10; r++) {
    const f = Rp[r], vu = f & (Rp[r - 1] | Rp[r + 1]), hu = f & ((f << 1) | (f >> 1)) & FULL;
    cont += POPC[vu & hu]; liveV += POPC[vu]; liveH += POPC[hu]; live += POPC[vu | hu];
    privV += POPC[vu & ~hu]; privH += POPC[hu & ~vu];
  }
  for (let t = 0; t < 5; t++) { exV[t] = 0; exH[t] = 0; ctV[t] = 0; ctH[t] = 0; }
  let mobV = 0, mobH = 0, splV = 0, splH = 0, c1V = 0, c1H = 0;
  for (let c = 1; c <= 10; c++) {
    const m = Cp[c]; if (!m) continue; mobV += NSEG[m];
    const hc = m & (Cp[c - 1] | Cp[c + 1]), rm = RUNS[m];
    for (let j = 0; j < rm.length; j++) {
      const run = rm[j], L = POPC[run], t = (L >> 1) - 1, k = POPC[run & hc];
      if (k === 0) exV[t]++; else { ctV[t]++; if (k === 1) c1V++; }
      if (L >= 5) { const inner = (run >> 2) & (run << 2) & run; if (inner & hc) splV++; }
    }
  }
  for (let r = 1; r <= 10; r++) {
    const m = Rp[r]; if (!m) continue; mobH += NSEG[m];
    const vc = m & (Rp[r - 1] | Rp[r + 1]), rm = RUNS[m];
    for (let j = 0; j < rm.length; j++) {
      const run = rm[j], L = POPC[run], t = (L >> 1) - 1, k = POPC[run & vc];
      if (k === 0) exH[t]++; else { ctH[t]++; if (k === 1) c1H++; }
      if (L >= 5) { const inner = (run >> 2) & (run << 2) & run; if (inner & vc) splH++; }
    }
  }
  const sEV = exV[0] + exV[1] + exV[2] + exV[3] + exV[4], sEH = exH[0] + exH[1] + exH[2] + exH[3] + exH[4];
  const sCV = ctV[0] + ctV[1] + ctV[2] + ctV[3] + ctV[4], sCH = ctH[0] + ctH[1] + ctH[2] + ctH[3] + ctH[4];
  const tV = exV[1] + 2 * exV[2] + 3 * exV[3] + 4 * exV[4], tH = exH[1] + 2 * exH[2] + 3 * exH[3] + 4 * exH[4];
  const RV = sEV + sCV, RH = sEH + sCH;
  let i = 0;
  G[i++] = 1; G[i++] = sEH - sEV; G[i++] = sCH - sCV; G[i++] = tV - tH; G[i++] = (mobV - mobH) / 20;
  G[i++] = cont / 20; G[i++] = live / 50; G[i++] = (privV - privH) / 10; G[i++] = splH - splV; G[i++] = c1H - c1V;
  for (let t = 0; t < 5; t++) { G[i++] = exV[t]; G[i++] = exH[t]; G[i++] = ctV[t]; G[i++] = ctH[t]; }
  G[i++] = RH - RV; G[i++] = (RH - RV) * live / 50; G[i++] = (sEH - sEV) * (1 - live / 100);
  G[i++] = Math.log1p(mobV) - Math.log1p(mobH);
  G[i++] = privV / 10; G[i++] = privH / 10; G[i++] = liveV / 20; G[i++] = liveH / 20; G[i++] = splV; G[i++] = splH;
  const d = sEH - sEV;
  G[i++] = d >= 0 ? 1 : 0; G[i++] = d >= 1 ? 1 : 0; G[i++] = d <= -1 ? 1 : 0; G[i++] = d <= -2 ? 1 : 0;
  return i;
}
// índices de padrão de todas as casas livres (devolve quantos, em PIDX)
const PIDX = new Int16Array(100);
function padroes() {
  let n = 0;
  for (let r = 1; r <= 10; r++) {
    let f = Rp[r];
    if (!f) continue;
    const up2 = Rp[r - 1] << 1, md2 = f << 1, dn2 = Rp[r + 1] << 1;
    while (f) {
      const b = f & -f; f ^= b; const c = CTZ[b];
      const x = (md2 >> c) & 7;
      PIDX[n++] = PAT[((up2 >> c) & 7) | ((x & 1) << 3) | ((x >> 2) << 4) | (((dn2 >> c) & 7) << 5)];
    }
  }
  return n;
}
// modelo: pesos já com normalização incorporada
let HID = 0, WG = null, WP = null, B1 = null, W2 = null, B2 = 0;
function carregarModelo(js) {
  HID = js.HID; const nIn = js.nIn, mu = js.mu, sd = js.sd;
  if (HID === 0) {
    const w = js.P[0]; B2 = js.P[1][0];
    WG = new Float64Array(NG); WP = new Float64Array(NPAT);
    for (let j = 0; j < nIn; j++) {
      const wj = w[j] / sd[j]; B2 -= wj * mu[j];
      if (j < NG) WG[j] = wj; else WP[j - NG] = wj * 0.1;
    }
  } else {
    const w1 = js.P[0], b1 = js.P[1], w2 = js.P[2];
    B1 = new Float64Array(HID); W2 = Float64Array.from(w2); B2 = js.P[3][0];
    WG = new Float64Array(HID * NG); WP = new Float64Array(HID * NPAT);
    for (let h = 0; h < HID; h++) {
      let b = b1[h];
      for (let j = 0; j < nIn; j++) {
        const wj = w1[h * nIn + j] / sd[j]; b -= wj * mu[j];
        if (j < NG) WG[h * NG + j] = wj; else WP[h * NPAT + j - NG] = wj * 0.1;
      }
      B1[h] = b;
    }
  }
}
const HB = new Float64Array(64);
// devolve o logit (perspetiva de quem tem a vez)
function avaliarML(R, C) {
  const ng = globais(R, C), np = padroes();
  if (HID === 0) {
    let z = B2;
    for (let j = 0; j < ng; j++) z += WG[j] * G[j];
    for (let k = 0; k < np; k++) z += WP[PIDX[k]];
    return z;
  }
  let z = B2;
  for (let h = 0; h < HID; h++) {
    let a = B1[h]; const og = h * NG, op = h * NPAT;
    for (let j = 0; j < ng; j++) a += WG[og + j] * G[j];
    for (let k = 0; k < np; k++) a += WP[op + PIDX[k]];
    z += W2[h] * (a > 0 ? a : 0.01 * a);
  }
  return z;
}
module.exports = { avaliarML, carregarModelo, NF, NPAT };
