'use strict';
// Características para a avaliação aprendida. Vista canónica: quem tem a vez joga na vertical
// (se for H, transpõe-se o tabuleiro). Entrada: R[0..9] máscaras de linhas livres na vista canónica.
const FULL = 0x3FF;
const RUNS = new Array(1024), POPC = new Uint8Array(1024), CTZ = new Int8Array(1024), NSEG = new Uint8Array(1024);
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
function transpor(rows) { const t = new Array(10).fill(0); for (let r = 0; r < 10; r++) for (let c = 0; c < 10; c++) if ((rows[r] >> c) & 1) t[c] |= 1 << r; return t; }

// nº de características globais
const NG = 64;
// padrões 3x3 (centro livre): 256 índices (8 vizinhos), agrupados pelas simetrias que preservam V/H
const PAT = new Int16Array(256); let NPAT = 0;
(function () {
  // vizinhos: 0 NW,1 N,2 NE,3 W,4 E,5 SW,6 S,7 SE
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
const NF = NG + NPAT;

const C = new Int32Array(12), Rp = new Int32Array(12);
// devolve Float32Array de NF características
function extrair(R, out) {
  out = out || new Float32Array(NF);
  out.fill(0);
  Rp[0] = 0; Rp[11] = 0; C.fill(0);
  for (let r = 0; r < 10; r++) { Rp[r + 1] = R[r]; for (let c = 0; c < 10; c++) if ((R[r] >> c) & 1) C[c + 1] |= 1 << r; }
  // utilizáveis
  let cont = 0, liveV = 0, liveH = 0, live = 0, privV = 0, privH = 0;
  const VU = new Int32Array(12), HU = new Int32Array(12);
  for (let r = 1; r <= 10; r++) {
    const f = Rp[r]; VU[r] = f & (Rp[r - 1] | Rp[r + 1]); HU[r] = f & ((f << 1) | (f >> 1)) & FULL;
    cont += POPC[VU[r] & HU[r]]; liveV += POPC[VU[r]]; liveH += POPC[HU[r]]; live += POPC[VU[r] | HU[r]];
    privV += POPC[VU[r] & ~HU[r]]; privH += POPC[HU[r] & ~VU[r]];
  }
  // runs verticais (minhas) e horizontais (do adversário)
  const exV = [0, 0, 0, 0, 0], exH = [0, 0, 0, 0, 0], ctV = [0, 0, 0, 0, 0], ctH = [0, 0, 0, 0, 0];
  let mobV = 0, mobH = 0, splV = 0, splH = 0, c1V = 0, c1H = 0;
  for (let c = 1; c <= 10; c++) {
    const m = C[c]; mobV += NSEG[m];
    const hc = m & (C[c - 1] | C[c + 1]);
    for (const run of RUNS[m]) {
      const L = POPC[run], t = (L >> 1) - 1, k = POPC[run & hc];
      if (k === 0) exV[t]++; else { ctV[t]++; if (k === 1) c1V++; }
      // casas disputadas onde o adversário pode partir esta run em duas >= 2
      const s = CTZ[run];
      for (let i = 2; i <= L - 3; i++) if ((hc >> (s + i)) & 1) { splV++; break; }
    }
  }
  for (let r = 1; r <= 10; r++) {
    const m = Rp[r]; mobH += NSEG[m];
    const vc = m & (Rp[r - 1] | Rp[r + 1]);
    for (const run of RUNS[m]) {
      const L = POPC[run], t = (L >> 1) - 1, k = POPC[run & vc];
      if (k === 0) exH[t]++; else { ctH[t]++; if (k === 1) c1H++; }
      const s = CTZ[run];
      for (let i = 2; i <= L - 3; i++) if ((vc >> (s + i)) & 1) { splH++; break; }
    }
  }
  const sum = a => a[0] + a[1] + a[2] + a[3] + a[4];
  const tem = a => a[1] + 2 * a[2] + 3 * a[3] + 4 * a[4];
  let i = 0;
  const RV = sum(exV) + sum(ctV), RH = sum(exH) + sum(ctH);
  out[i++] = 1;                                  // viés
  out[i++] = sum(exH) - sum(exV);                // runs exclusivas (adv - minhas)
  out[i++] = sum(ctH) - sum(ctV);                // runs disputadas
  out[i++] = tem(exV) - tem(exH);                // tempos de reserva
  out[i++] = (mobV - mobH) / 20;
  out[i++] = cont / 20;
  out[i++] = live / 50;
  out[i++] = (privV - privH) / 10;
  out[i++] = splH - splV;
  out[i++] = c1H - c1V;
  for (let t = 0; t < 5; t++) { out[i++] = exV[t]; out[i++] = exH[t]; out[i++] = ctV[t]; out[i++] = ctH[t]; }  // 20
  out[i++] = RH - RV;
  out[i++] = (RH - RV) * live / 50;
  out[i++] = (sum(exH) - sum(exV)) * (1 - live / 100);
  out[i++] = Math.log1p(mobV) - Math.log1p(mobH);
  out[i++] = privV / 10; out[i++] = privH / 10;
  out[i++] = liveV / 20; out[i++] = liveH / 20;
  out[i++] = splV; out[i++] = splH;
  // paridade das runs exclusivas
  const d = sum(exH) - sum(exV);
  out[i++] = d >= 0 ? 1 : 0; out[i++] = d >= 1 ? 1 : 0; out[i++] = d <= -1 ? 1 : 0; out[i++] = d <= -2 ? 1 : 0;
  // padrões 3x3
  for (let r = 1; r <= 10; r++) {
    let f = Rp[r];
    while (f) {
      const b = f & -f; f ^= b; const c = CTZ[b];
      const up = Rp[r - 1], dn = Rp[r + 1], md = Rp[r];
      const bit = (m, cc) => (cc >= 0 && cc < 10 && ((m >> cc) & 1)) ? 1 : 0;
      const n = bit(up, c - 1) | bit(up, c) << 1 | bit(up, c + 1) << 2 | bit(md, c - 1) << 3 | bit(md, c + 1) << 4 | bit(dn, c - 1) << 5 | bit(dn, c) << 6 | bit(dn, c + 1) << 7;
      out[NG + PAT[n]] += 0.1;
    }
  }
  return out;
}
module.exports = { extrair, transpor, NF, NG, NPAT };
