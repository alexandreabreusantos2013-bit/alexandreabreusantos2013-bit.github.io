'use strict';
/*
 * bot_novo.js — bot de Quelhas (10x10, misère: quem faz a última jogada PERDE).
 * Interface: module.exports = { escolherJogada(tab, orient, opc) }
 *
 * Como decide uma jogada (opc.tempoMs é limite duro; usa no máximo min(0.8*tempo, tempo-90) ms):
 *   1. livro de aberturas (posições fixas, com as 4 simetrias que preservam V/H);
 *   2. alfa-beta (PVS + TT + killers + history) com avaliação aprendida, para ordenar as jogadas da raiz;
 *   3. verificação exata das melhores jogadas pelo solver por regiões, em rondas com top-K e orçamento
 *      de nós crescentes: joga uma vitória provada, nunca joga uma jogada provada perdedora se houver outra.
 *
 * Solver exato: o tabuleiro decompõe-se em regiões independentes (componentes 4-conexas de casas livres).
 * Uma região em linha reta só serve a um jogador (run exclusiva) e resume-se à sua classe floor(L/2)-1
 * (jogadas de espera que permite): bastam 2 jogadas por jogador nessas runs (fechar a de menor classe,
 * encurtar em 2 a de menor classe >= 1). As outras regiões ficam num pool imutável; uma jogada só
 * recalcula a região onde foi feita. Chave da TT: soma dos hashes canónicos das regiões (invariantes por
 * translação e pelas 2 reflexões que preservam V/H; com H a jogar usa-se a transposta) + contadores.
 *
 * Avaliação: regressão logística sobre 44 características globais (runs exclusivas/disputadas por classe,
 * mobilidade, casas disputadas e privadas, runs partíveis...) + 88 classes de padrões 3x3, treinada com
 * rótulos do solver exato (posições até ~80 casas vivas) e com o resultado do 1.º ponto provado em
 * partidas de auto-jogo (posições anteriores).
 *
 * Teorema usado (exato): sem casas disputadas, quem tem a vez ganha sse tiver <= runs que o adversário.
 *
 * Modos extra:
 *   node bot_novo.js --verificar
 *       solver vs força bruta e vs uma referência exata sem abstrações; legalidade e tempo das jogadas
 *   node bot_novo.js --treinar [--iter 60] [--tempo 100] [--contra outro_bot.js] [--seed 1]
 *       afina por SPSA os parâmetros P (escala da avaliação e frações de tempo) e imprime a linha a colar
 */

// ---------- Parâmetros afináveis ----------
// [0] escala da avaliação (logit -> pontos)   [1..4] fração do tempo para a alfa-beta antes da verificação,
// por nº de casas vivas: <=72, <=82, <=90, >90 (com <=60 vai direto ao solver)
let P = [100, 0.1, 0.15, 0.25, 0.45];

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
function carregarSolver() {   // nível 0 a partir de rowM
  poolTop = 0; NL[0] = 0;
  for (let i = 0; i < 5; i++) { CNTV[i] = 0; CNTH[i] = 0; }
  S[0] = 0; S[11] = 0;
  for (let r = 0; r < 10; r++) S[r + 1] = rowM[r];
  decompor(0);
}
const SBITS = 23, SMASK = (1 << SBITS) - 1;
const sKey = new Int32Array(1 << SBITS), sVal = new Uint8Array(1 << SBITS);   // valor: 6 bits extra da chave | 1 ganha / 2 perde
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
  const ei = k1 & SMASK, ev = sVal[ei], tag = (k1 >>> 26) << 2;
  if (ev !== 0 && sKey[ei] === k2 && (ev & 0xFC) === tag) return (ev & 3) === 1;
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
  sKey[ei] = k2; sVal[ei] = tag | (win ? 1 : 2);
  return win;
}

// =====================================================================================
// Avaliação aprendida (vista canónica: quem tem a vez joga na vertical; com H a jogar usa-se a transposta)
// =====================================================================================
const PAT = new Int16Array(256); let NPAT = 0;   // padrão 3x3 à volta de uma casa livre (8 vizinhos), módulo reflexões
(function () {
  const flipV = [5, 6, 7, 3, 4, 0, 1, 2], flipH = [2, 1, 0, 4, 3, 7, 6, 5];
  const ap = (m, perm) => { let r = 0; for (let i = 0; i < 8; i++) if ((m >> i) & 1) r |= 1 << perm[i]; return r; };
  const cls = new Map();
  for (let m = 0; m < 256; m++) {
    const k = Math.min(m, ap(m, flipV), ap(m, flipH), ap(ap(m, flipV), flipH));
    if (!cls.has(k)) cls.set(k, NPAT++);
    PAT[m] = cls.get(k);
  }
})();
const NG = 64;
const Rp = new Int32Array(12), Cp = new Int32Array(12), G = new Float64Array(NG);
const exV = new Int32Array(5), exH = new Int32Array(5), ctV = new Int32Array(5), ctH = new Int32Array(5);
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
      if (L >= 5 && ((run >> 2) & (run << 2) & run & hc)) splV++;
    }
  }
  for (let r = 1; r <= 10; r++) {
    const m = Rp[r]; if (!m) continue; mobH += NSEG[m];
    const vc = m & (Rp[r - 1] | Rp[r + 1]), rm = RUNS[m];
    for (let j = 0; j < rm.length; j++) {
      const run = rm[j], L = POPC[run], t = (L >> 1) - 1, k = POPC[run & vc];
      if (k === 0) exH[t]++; else { ctH[t]++; if (k === 1) c1H++; }
      if (L >= 5 && ((run >> 2) & (run << 2) & run & vc)) splH++;
    }
  }
  const sEV = exV[0] + exV[1] + exV[2] + exV[3] + exV[4], sEH = exH[0] + exH[1] + exH[2] + exH[3] + exH[4];
  const sCV = ctV[0] + ctV[1] + ctV[2] + ctV[3] + ctV[4], sCH = ctH[0] + ctH[1] + ctH[2] + ctH[3] + ctH[4];
  const tV = exV[1] + 2 * exV[2] + 3 * exV[3] + 4 * exV[4], tH = exH[1] + 2 * exH[2] + 3 * exH[3] + 4 * exH[4];
  const RV = sEV + sCV, RH = sEH + sCH, d = sEH - sEV;
  let i = 0;
  G[i++] = 1; G[i++] = d; G[i++] = sCH - sCV; G[i++] = tV - tH; G[i++] = (mobV - mobH) / 20;
  G[i++] = cont / 20; G[i++] = live / 50; G[i++] = (privV - privH) / 10; G[i++] = splH - splV; G[i++] = c1H - c1V;
  for (let t = 0; t < 5; t++) { G[i++] = exV[t]; G[i++] = exH[t]; G[i++] = ctV[t]; G[i++] = ctH[t]; }
  G[i++] = RH - RV; G[i++] = (RH - RV) * live / 50; G[i++] = d * (1 - live / 100);
  G[i++] = Math.log1p(mobV) - Math.log1p(mobH);
  G[i++] = privV / 10; G[i++] = privH / 10; G[i++] = liveV / 20; G[i++] = liveH / 20; G[i++] = splV; G[i++] = splH;
  G[i++] = d >= 0 ? 1 : 0; G[i++] = d >= 1 ? 1 : 0; G[i++] = d <= -1 ? 1 : 0; G[i++] = d <= -2 ? 1 : 0;
  return i;
}
// logit da vitória de quem tem a vez (R/C: linhas/colunas da vista canónica)
function avaliarML(R, C) {
  const ng = globais(R, C);
  let z = MOD_B;
  for (let j = 0; j < ng; j++) z += MOD_WG[j] * G[j];
  for (let r = 1; r <= 10; r++) {
    let f = Rp[r];
    if (!f) continue;
    const up2 = Rp[r - 1] << 1, md2 = f << 1, dn2 = Rp[r + 1] << 1;
    while (f) {
      const b = f & -f; f ^= b; const c = CTZ[b], x = (md2 >> c) & 7;
      z += MOD_WP[PAT[((up2 >> c) & 7) | ((x & 1) << 3) | ((x >> 2) << 4) | (((dn2 >> c) & 7) << 5)]];
    }
  }
  return z;
}
// @@MODELO@@
const MODELO_EMB = { HID: 0, WG: [0.075787,0.29564,0.066202,-0.070899,-0.20225,0.099036,0.98332,0.84083,0.22483,0.31136,-0.6147,0.43994,-0.076476,0.10132,-0.15394,0.045603,0.17538,-0.12493,0.091686,-0.065675,0.30818,-0.23013,-0.28783,0.21072,0.29995,-0.2383,-0.19253,-0.039544,0.23404,-0.37972,0.081734,-0.0365,-0.54545,5.9255,0.8352,-0.56776,0.4895,-0.18577,-0.06245,0.017622,-0.51225,-1.0328,0.51225,0.29975,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], WP: [0.10393,0.049128,-0.19158,-0.26807,-0.5993,-0.11367,0.20041,0.29086,-0.074826,0.0046894,0.12326,0.11298,0.22139,0.088714,-0.14842,-0.17116,0.63274,0.018493,0.17991,-0.021795,1.6962,-0.11413,-0.1131,0,0,0.19963,-1.7395,-0.25561,-0.2272,0.05644,0.25868,1.1251,-0.055038,0.17686,4.8301,0.1349,-0.87199,1.0582,0.063226,0.15714,-0.091496,0.79795,0.17678,0.33221,-0.31914,0.2285,0.038197,0.195,0.245,-3.8972,0.23436,-0.86726,0.064239,1.8384,-0.56862,0.031001,0,-0.019324,-1.3246,-0.30019,-0.24412,-1.4412,-0.26856,0.22342,0.045373,-0.014479,-0.084601,-0.043695,3.1215,-0.66666,0.028416,0.48444,0.026959,0.051447,-0.0076538,0,1.4831,-1.5049,-0.15106,-0.11042,-0.091003,0.16804,0.05829,0.00041862], B1: [], W2: [], B2: -1.9885 };
// @@FIM_MODELO@@
const MOD_B = MODELO_EMB.B2, MOD_WG = Float64Array.from(MODELO_EMB.WG), MOD_WP = Float64Array.from(MODELO_EMB.WP);

// =====================================================================================
// Alfa-beta
// =====================================================================================
const rowM = new Int32Array(10), colM = new Int32Array(10);
let h1 = 0, h2 = 0, side = 0;          // side 0 = V, 1 = H
let deadline = 0, nodes = 0;
let TSIZE, TMASK, tKey, tScore, tMove, tDepth, tFlag;
function resizeTT(bits) {
  TSIZE = 1 << bits; TMASK = TSIZE - 1;
  tKey = new Int32Array(TSIZE); tScore = new Int32Array(TSIZE); tMove = new Int16Array(TSIZE);
  tDepth = new Int8Array(TSIZE); tFlag = new Uint8Array(TSIZE);
}
resizeTT(20);
const HIST = new Int32Array(8192), K1 = new Int32Array(128), K2 = new Int32Array(128);
const MB = []; for (let i = 0; i < 128; i++) MB.push(new Int32Array(512));
function limparTT() { tKey.fill(0); tFlag.fill(0); HIST.fill(0); sVal.fill(0); }

// Jogada: dir<<12 | linha<<8 | inicio<<4 | comprimento   (dir 0 = V na coluna 'linha', 1 = H na linha 'linha')
function make(m) {
  const line = (m >> 8) & 15, s = (m >> 4) & 15, l = m & 15, seg = ((1 << l) - 1) << s, bit = 1 << line;
  if ((m >> 12) === 0) {
    colM[line] &= ~seg;
    for (let r = s; r < s + l; r++) { rowM[r] &= ~bit; const k = r * 10 + line; h1 ^= ZA[k]; h2 ^= ZB[k]; }
  } else {
    rowM[line] &= ~seg;
    for (let c = s; c < s + l; c++) { colM[c] &= ~bit; const k = line * 10 + c; h1 ^= ZA[k]; h2 ^= ZB[k]; }
  }
  h1 ^= SA; h2 ^= SB; side ^= 1;
}
function unmake(m) {
  side ^= 1; h1 ^= SA; h2 ^= SB;
  const line = (m >> 8) & 15, s = (m >> 4) & 15, l = m & 15, seg = ((1 << l) - 1) << s, bit = 1 << line;
  if ((m >> 12) === 0) {
    colM[line] |= seg;
    for (let r = s; r < s + l; r++) { rowM[r] |= bit; const k = r * 10 + line; h1 ^= ZA[k]; h2 ^= ZB[k]; }
  } else {
    rowM[line] |= seg;
    for (let c = s; c < s + l; c++) { colM[c] |= bit; const k = line * 10 + c; h1 ^= ZA[k]; h2 ^= ZB[k]; }
  }
}
function setup(tab, orient) {
  h1 = 0; h2 = 0;
  for (let i = 0; i < 10; i++) { rowM[i] = 0; colM[i] = 0; }
  for (let r = 0; r < 10; r++) for (let c = 0; c < 10; c++) {
    if (!tab[r][c]) { rowM[r] |= 1 << c; colM[c] |= 1 << r; }
    else { h1 ^= ZA[r * 10 + c]; h2 ^= ZB[r * 10 + c]; }
  }
  side = orient === 'H' ? 1 : 0;
  if (side === 1) { h1 ^= SA; h2 ^= SB; }
}
function avaliarAqui() { return Math.round(P[0] * (side === 0 ? avaliarML(rowM, colM) : avaliarML(colM, rowM))); }

// características rápidas para a alfa-beta: casas disputadas, runs, mobilidade
const vuCol = new Int32Array(10), huRow = new Int32Array(10), contCol = new Int32Array(10), contRow = new Int32Array(10);
let fRv = 0, fRh = 0, fMv = 0, fMh = 0, fCont = 0, fLive = 0;
function features() {
  for (let i = 0; i < 10; i++) {
    const m = colM[i]; vuCol[i] = m & ((m << 1) | (m >> 1)) & FULL; contCol[i] = 0;
    const n = rowM[i]; huRow[i] = n & ((n << 1) | (n >> 1)) & FULL; contRow[i] = 0;
  }
  let cont = 0, live = 0;
  for (let r = 0; r < 10; r++) {
    let hu = huRow[r]; live += POPC[hu];
    while (hu) {
      const b = hu & -hu; hu ^= b; const c = CTZ[b];
      if ((vuCol[c] >> r) & 1) { contCol[c] |= 1 << r; contRow[r] |= b; cont++; }
    }
  }
  let R = 0, M = 0;
  for (let c = 0; c < 10; c++) { const m = colM[c]; live += POPC[vuCol[c]]; M += NSEG[m]; R += NRUN[m]; }
  fRv = R; fMv = M;
  R = 0; M = 0;
  for (let r = 0; r < 10; r++) { const m = rowM[r]; M += NSEG[m]; R += NRUN[m]; }
  fRh = R; fMh = M; fCont = cont; fLive = live - cont;
}
// geração com eliminação de jogadas equivalentes em runs exclusivas (mesmo comprimento / mesmas sobras)
const stamp = new Int32Array(128); let stampId = 0;
function genRun(buf, n, base, s0, L, excl) {
  if (!excl) {
    for (let i = 0; i <= L - 2; i++) for (let l = 2; i + l <= L; l++) buf[n++] = base | ((s0 + i) << 4) | l;
    return n;
  }
  stampId++;
  for (let i = 0; i <= L - 2; i++) for (let l = 2; i + l <= L; l++) {
    let a = i, b = L - i - l; if (a < 2) a = 0; if (b < 2) b = 0; if (a > b) { const t = a; a = b; b = t; }
    const key = a * 11 + b; if (stamp[key] === stampId) continue; stamp[key] = stampId;
    buf[n++] = base | ((s0 + i) << 4) | l;
  }
  return n;
}
function gerar(buf) { // requer features() da posição atual
  let n = 0, seen = 0;
  if (side === 0) {
    for (let c = 0; c < 10; c++) {
      const m = colM[c], k = NRUN[m]; if (!k) continue;
      const rm = RUNS[m], cc = contCol[c], base = c << 8;
      for (let j = 0; j < k; j++) {
        const run = rm[j], L = POPC[run], ex = (run & cc) === 0;
        if (ex) { if ((seen >> L) & 1) continue; seen |= 1 << L; }
        n = genRun(buf, n, base, CTZ[run], L, ex);
      }
    }
  } else {
    for (let r = 0; r < 10; r++) {
      const m = rowM[r], k = NRUN[m]; if (!k) continue;
      const rm = RUNS[m], cc = contRow[r], base = (1 << 12) | (r << 8);
      for (let j = 0; j < k; j++) {
        const run = rm[j], L = POPC[run], ex = (run & cc) === 0;
        if (ex) { if ((seen >> L) & 1) continue; seen |= 1 << L; }
        n = genRun(buf, n, base, CTZ[run], L, ex);
      }
    }
  }
  return n;
}
// ordenação rápida: partir runs do adversário (+), não criar runs minhas (-)
function rapido(mv) {
  const line = (mv >> 8) & 15, s = (mv >> 4) & 15, l = mv & 15, seg = ((1 << l) - 1) << s, bit = 1 << line;
  let my, op = 0;
  if ((mv >> 12) === 0) {
    const b = colM[line]; my = NRUN[b & ~seg] - NRUN[b];
    for (let r = s; r < s + l; r++) { const x = rowM[r]; op += NRUN[x & ~bit] - NRUN[x]; }
  } else {
    const b = rowM[line]; my = NRUN[b & ~seg] - NRUN[b];
    for (let c = s; c < s + l; c++) { const x = colM[c]; op += NRUN[x & ~bit] - NRUN[x]; }
  }
  return op * 2 - my * 3;
}
function search(depth, alpha, beta, ply) {
  if ((++nodes & 255) === 0 && Date.now() >= deadline) throw ABORT;
  features();
  const Mme = side === 0 ? fMv : fMh;
  if (Mme === 0) return WIN - ply;
  if (fCont === 0) {
    const Rme = side === 0 ? fRv : fRh, Rop = side === 0 ? fRh : fRv;
    return Rme <= Rop ? WIN - (ply + 2 * Rme) : -(WIN - (ply + 2 * Rop + 1));
  }
  if (depth <= 0) return avaliarAqui();
  const ti = h1 & TMASK; let ttMove = 0;
  if (tFlag[ti] !== 0 && tKey[ti] === h2) {
    ttMove = tMove[ti];
    if (tDepth[ti] >= depth) {
      let s = tScore[ti]; if (s > MATE_TH) s -= ply; else if (s < -MATE_TH) s += ply;
      const f = tFlag[ti];
      if (f === EXACT) return s;
      if (f === LOWER && s >= beta) return s;
      if (f === UPPER && s <= alpha) return s;
    }
  }
  const buf = MB[ply], n = gerar(buf), k1 = K1[ply], k2 = K2[ply];
  for (let i = 0; i < n; i++) {
    const mv = buf[i]; let sc;
    if (mv === ttMove) sc = 120000; else if (mv === k1) sc = 100000; else if (mv === k2) sc = 99000;
    else {
      sc = rapido(mv) * 100 + (mv & 15) * 3 + (HIST[mv] >> 10);
      if (sc > 90000) sc = 90000; else if (sc < -130000) sc = -130000;
    }
    buf[i] = ((sc + 131072) << 13) | mv;
  }
  buf.subarray(0, n).sort();
  const a0 = alpha; let best = -INF, bestMv = 0, searched = 0;
  for (let i = n - 1; i >= 0; i--) {
    const mv = buf[i] & 8191;
    make(mv);
    let sc;
    if (searched === 0) sc = -search(depth - 1, -beta, -alpha, ply + 1);
    else {
      let r = 0;
      if (depth >= 3 && searched >= 4 && mv !== k1 && mv !== k2) r = searched >= 12 ? 2 : 1;
      if (r > depth - 1) r = depth - 1;
      sc = -search(depth - 1 - r, -alpha - 1, -alpha, ply + 1);
      if (sc > alpha && r > 0) sc = -search(depth - 1, -alpha - 1, -alpha, ply + 1);
      if (sc > alpha && sc < beta) sc = -search(depth - 1, -beta, -alpha, ply + 1);
    }
    unmake(mv); searched++;
    if (sc > best) {
      best = sc; bestMv = mv;
      if (sc > alpha) {
        alpha = sc;
        if (alpha >= beta) {
          if (mv !== K1[ply]) { K2[ply] = K1[ply]; K1[ply] = mv; }
          HIST[mv] = Math.min(HIST[mv] + depth * depth, 65535);
          break;
        }
      }
    }
  }
  let st = best; if (st > MATE_TH) st += ply; else if (st < -MATE_TH) st -= ply;
  if (tKey[ti] !== h2 || tDepth[ti] <= depth) {
    tKey[ti] = h2; tScore[ti] = st; tDepth[ti] = depth; tMove[ti] = bestMv;
    tFlag[ti] = best <= a0 ? UPPER : (best >= beta ? LOWER : EXACT);
  }
  return best;
}
// aprofundamento iterativo na raiz; ord (lista {mv, sc}) fica ordenada com a melhor primeiro.
// Atenção: ao ser interrompida, a pesquisa deixa o tabuleiro a meio (quem chama tem de repor).
function pensar(ord, t0, budget) {
  let best = ord[0].mv;
  for (let d = 1; d <= 60; d++) {
    let alpha = -INF, cur = 0, curSc = -INF;
    try {
      for (let i = 0; i < ord.length; i++) {
        const mv = ord[i].mv; make(mv);
        let sc;
        if (i === 0) sc = -search(d - 1, -INF, -alpha, 1);
        else {
          sc = -search(d - 1, -alpha - 1, -alpha, 1);
          if (sc > alpha) sc = -search(d - 1, -INF, -alpha, 1);
        }
        unmake(mv); ord[i].sc = sc;
        if (sc > curSc) { curSc = sc; cur = mv; if (sc > alpha) alpha = sc; }
      }
    } catch (e) {
      if (e !== ABORT) throw e;
      if (cur) best = cur;
      break;
    }
    best = cur;
    ord.sort((a, b) => ((b.mv === cur) - (a.mv === cur)) || (b.sc - a.sc));
    if (curSc > MATE_TH || curSc < -MATE_TH) break;
    if (Date.now() - t0 > budget * 0.45) break;
  }
  ord.sort((a, b) => ((b.mv === best) - (a.mv === best)) || (b.sc - a.sc));
  return best;
}
// verificação exata da lista ordenada: rondas com top-K e orçamento de nós crescentes.
// Devolve { ganha: mv } (vitória provada), { perdida: mv } (todas perdem: devolve a de refutação mais cara)
// ou null; marca em perde as jogadas provadas perdedoras.
function verificarRaiz(ord, tFim, perde) {
  deadline = tFim;
  const n = ord.length, st = new Int8Array(n), custo = new Float64Array(n);
  let K = Math.min(n, 4), B = 4000;
  for (let ronda = 0; ronda < 12; ronda++) {
    let desc = 0;
    for (let i = 0; i < K; i++) {
      if (st[i] !== 0) continue;
      if (Date.now() >= tFim) return null;
      const mv = ord[i].mv, n0 = sNodes;
      make(mv); carregarSolver(); sNodeLim = sNodes + B;
      let w = -1;
      try { w = resolve(0, side) ? 1 : 0; } catch (e) { if (e !== ABORT) { unmake(mv); sNodeLim = Infinity; throw e; } }
      unmake(mv); sNodeLim = Infinity;
      custo[i] += sNodes - n0;
      if (w === 0) return { ganha: mv };
      if (w === 1) { st[i] = 2; perde.add(mv); } else desc++;
    }
    if (desc === 0 && K === n) {
      let b = 0; for (let i = 1; i < n; i++) if (custo[i] > custo[b]) b = i;
      return { perdida: ord[b].mv };
    }
    K = Math.min(n, K * 2); B *= 4;
  }
  return null;
}

// =====================================================================================
// Livro de aberturas: chave = linhas livres (hex) + vez; procura nas 4 simetrias que preservam V/H
// =====================================================================================
// @@LIVRO@@
const LIVRO = {};
// @@FIM_LIVRO@@
const REV10 = new Int16Array(1024); for (let m = 0; m < 1024; m++) REV10[m] = REVW[10 * 1024 + m];
function chaveLivro(rows, o) { let k = ''; for (let r = 0; r < 10; r++) k += (rows[r] | 1024).toString(16); return k + o; }
function consultarLivro(o) {
  for (let sym = 0; sym < 4; sym++) {
    const rows = [];
    for (let r = 0; r < 10; r++) { let m = rowM[(sym & 1) ? 9 - r : r]; if (sym & 2) m = REV10[m]; rows.push(m); }
    const e = LIVRO[chaveLivro(rows, o)];
    if (e === undefined) continue;
    // e = [dir, linha, inicio, comprimento] no tabuleiro transformado -> desfazer a simetria
    let [d, line, s, l] = e;
    if (d === 0) { if (sym & 2) line = 9 - line; if (sym & 1) s = 10 - s - l; }
    else { if (sym & 1) line = 9 - line; if (sym & 2) s = 10 - s - l; }
    return (d << 12) | (line << 8) | (s << 4) | l;
  }
  return 0;
}

// ---------- Utilitários sobre a matriz ----------
function casas(mv) {
  const line = (mv >> 8) & 15, s = (mv >> 4) & 15, l = mv & 15, out = [];
  for (let k = 0; k < l; k++) out.push((mv >> 12) === 0 ? [s + k, line] : [line, s + k]);
  return out;
}
function listar(tab, o) {
  const out = [];
  for (let a = 0; a < 10; a++) for (let s = 0; s < 10; s++) {
    const livre = i => (o === 'V' ? !tab[i][a] : !tab[a][i]);
    if (!livre(s)) continue;
    let e = s; while (e < 10 && livre(e)) e++;
    for (let l = 2; s + l <= e; l++) {
      const cs = []; for (let k = 0; k < l; k++) cs.push(o === 'V' ? [s + k, a] : [a, s + k]);
      out.push(cs);
    }
  }
  return out;
}
function valida(tab, o, cs) {
  if (!Array.isArray(cs) || cs.length < 2) return false;
  for (const p of cs) {
    if (!Array.isArray(p)) return false;
    const r = p[0], c = p[1];
    if (!Number.isInteger(r) || !Number.isInteger(c) || r < 0 || r > 9 || c < 0 || c > 9 || tab[r][c]) return false;
  }
  const fixo = o === 'V' ? 1 : 0, var_ = o === 'V' ? 0 : 1;
  if (cs.some(p => p[fixo] !== cs[0][fixo])) return false;
  const v = cs.map(p => p[var_]).sort((a, b) => a - b);
  for (let i = 1; i < v.length; i++) if (v[i] !== v[0] + i) return false;
  return true;
}
function reserva(tab, o) { const L = listar(tab, o); return L.length ? L[0] : []; }

// ---------- Interface ----------
let ultimo = null;   // diagnóstico da última jogada
let usarLivro = true;
function escolherJogada(tab, orient, opc) {
  const t0 = Date.now();
  opc = opc || {};
  const tempo = (typeof opc.tempoMs === 'number' && opc.tempoMs > 0) ? opc.tempoMs : 500;
  const rng = typeof opc.rng === 'function' ? opc.rng : Math.random;
  const budget = Math.max(10, Math.min(tempo * 0.8, tempo - 90));
  let res;
  ultimo = { estado: '?' };
  try {
    for (let i = 0; i < 8192; i++) HIST[i] >>= 1;
    K1.fill(0); K2.fill(0); nodes = 0;
    setup(tab, orient);
    features();
    const n0 = gerar(MB[0]);
    if (n0 === 0) return [];
    const raiz = Array.from(MB[0].subarray(0, n0));
    let mv = usarLivro ? consultarLivro(orient) : 0;
    if (mv && raiz.indexOf(mv) < 0) mv = 0;      // só aceita jogadas do livro que existam aqui
    if (mv) ultimo.estado = 'livro';
    else if (raiz.length === 1) mv = raiz[0];
    else {
      const L = fLive;
      ultimo.live = L;
      // ordenação inicial: avaliação depois de 1 jogada (+ ruído mínimo para desempatar)
      const ord = [];
      for (const x of raiz) { make(x); const z = side === 0 ? avaliarML(rowM, colM) : avaliarML(colM, rowM); unmake(x); ord.push({ mv: x, sc: -Math.round(P[0] * z) + rng() * 2 }); }
      ord.sort((a, b) => b.sc - a.sc);
      const fab = L <= 60 ? 0 : L <= 72 ? P[1] : L <= 82 ? P[2] : L <= 90 ? P[3] : P[4];
      if (fab > 0) {
        deadline = t0 + budget * fab;
        pensar(ord, t0, budget * fab);
        setup(tab, orient);           // repor o tabuleiro (a alfa-beta pode ter sido interrompida a meio)
      }
      const perde = new Set();
      const r = verificarRaiz(ord, t0 + budget, perde);
      ultimo.sNodes = sNodes;
      if (r && r.ganha !== undefined) { mv = r.ganha; ultimo.estado = 'ganha'; }
      else if (r && r.perdida !== undefined) { mv = r.perdida; ultimo.estado = 'perdida'; }
      else {
        ultimo.estado = 'aberta';
        for (const x of ord) if (!perde.has(x.mv)) { mv = x.mv; break; }
        if (!mv) mv = ord[0].mv;
      }
    }
    res = casas(mv);
  } catch (e) { res = null; ultimo.erro = String(e && e.stack || e); }
  if (!valida(tab, orient, res)) { res = reserva(tab, orient); ultimo.reserva = true; }
  return res;
}

module.exports = { escolherJogada };
Object.defineProperty(module.exports, '_ultimo', { get: () => ultimo, enumerable: false });

// =====================================================================================
// Modos de verificação e treino
// =====================================================================================
function mulberry32(a) {
  return function () {
    a |= 0; a = a + 0x6D2B79F5 | 0;
    let t = Math.imul(a ^ a >>> 15, 1 | a);
    t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t;
    return ((t ^ t >>> 14) >>> 0) / 4294967296;
  };
}
function tabVazio() { return [...Array(10)].map(() => Array(10).fill(0)); }
function aplicar(tab, cs, o) { for (const [r, c] of cs) tab[r][c] = o === 'V' ? 1 : 2; }
function abertura(rng, k) {
  const tab = tabVazio(), seq = []; let o = 'V';
  for (let i = 0; i < k; i++) {
    const L = listar(tab, o); if (!L.length) break;
    const cs = L[Math.floor(rng() * L.length)]; aplicar(tab, cs, o); seq.push(cs);
    o = o === 'V' ? 'H' : 'V';
  }
  return seq;
}
function jogarPartida(botV, botH, tempo, rng, ab) {  // devolve o vencedor 'V' ou 'H'
  const tab = tabVazio(); let o = 'V';
  for (const cs of ab) { aplicar(tab, cs, o); o = o === 'V' ? 'H' : 'V'; }
  for (let k = 0; k < 200; k++) {
    if (listar(tab, o).length === 0) return o;          // misère: sem jogada na vez = ganha
    const bot = o === 'V' ? botV : botH; let cs;
    try { cs = bot(tab.map(r => r.slice()), o, { tempoMs: tempo, rng }); } catch (e) { cs = null; }
    if (!valida(tab, o, cs)) return o === 'V' ? 'H' : 'V';
    aplicar(tab, cs, o); o = o === 'V' ? 'H' : 'V';
  }
  return o;
}
// solver exato de referência, sem abstrações nem chaves canónicas (memo com o tabuleiro inteiro)
function referencia(rows, o, memo) {
  const key = rows.join(',') + o, m = memo.get(key); if (m !== undefined) return m;
  const free = (r, c) => r >= 0 && r < 10 && c >= 0 && c < 10 && ((rows[r] >> c) & 1);
  let cont = 0, vr = 0, hr = 0;
  for (let r = 0; r < 10; r++) for (let c = 0; c < 10; c++) if (free(r, c)) {
    const v = free(r - 1, c) || free(r + 1, c), h = free(r, c - 1) || free(r, c + 1);
    if (v && h) cont++;
    if (v && !free(r - 1, c)) vr++;
    if (h && !free(r, c - 1)) hr++;
  }
  let win;
  if (cont === 0) win = o === 'V' ? vr <= hr : hr <= vr;
  else {
    win = false;
    for (let a = 0; a < 10 && !win; a++) for (let s = 0; s < 10 && !win; s++) {
      let e = s; while (e < 10 && (o === 'V' ? (rows[e] >> a) & 1 : (rows[a] >> e) & 1)) e++;
      for (let l = 2; s + l <= e && !win; l++) {
        const nr = rows.slice();
        if (o === 'V') for (let k = 0; k < l; k++) nr[s + k] &= ~(1 << a); else nr[a] &= ~(((1 << l) - 1) << s);
        if (!referencia(nr, o === 'V' ? 'H' : 'V', memo)) win = true;
      }
    }
  }
  memo.set(key, win); return win;
}
function forcaBruta(memo) {
  const key = h1 + ':' + h2, m = memo.get(key); if (m !== undefined) return m;
  const mv = [];
  if (side === 0) { for (let c = 0; c < 10; c++) for (const x of SEGS[colM[c]]) mv.push((c << 8) | x); }
  else { for (let r = 0; r < 10; r++) for (const x of SEGS[rowM[r]]) mv.push((1 << 12) | (r << 8) | x); }
  let win = mv.length === 0;
  for (const x of mv) { if (win) break; make(x); const w = forcaBruta(memo); unmake(x); if (!w) win = true; }
  memo.set(key, win); return win;
}
function resolverTab(tab, o) { setup(tab, o); carregarSolver(); deadline = Infinity; sNodeLim = Infinity; return resolve(0, side); }
function verificar() {
  const rng = mulberry32(7);
  let ok = 0, mal = 0;
  for (let t = 0; t < 400; t++) {
    const tab = tabVazio(), p = 0.7 + rng() * 0.15;
    for (let r = 0; r < 10; r++) for (let c = 0; c < 10; c++) if (rng() < p) tab[r][c] = rng() < 0.5 ? 1 : 2;
    for (const o of ['V', 'H']) {
      sVal.fill(0); const a = resolverTab(tab, o);
      setup(tab, o); const b = forcaBruta(new Map());
      if (a === b) ok++;
      else { mal++; if (mal <= 3) { console.log('DIVERGÊNCIA vez=' + o, 'solver=' + a, 'bruta=' + b); console.log(tab.map(r => r.join('')).join('\n')); } }
    }
  }
  console.log(`Solver exato vs força bruta: ${ok} certos, ${mal} errados`);
  // posições maiores (até ~34 casas vivas), vindas de jogo aleatório, contra a referência sem abstrações
  ok = 0; mal = 0;
  for (let t = 0; t < 60; t++) {
    const tab = tabVazio(), seq = abertura(rng, 14 + Math.floor(rng() * 8));
    seq.forEach((cs, i) => aplicar(tab, cs, i % 2 ? 'H' : 'V'));
    let live = 0; for (let r = 0; r < 10; r++) for (let c = 0; c < 10; c++) if (!tab[r][c] && ((r > 0 && !tab[r - 1][c]) || (r < 9 && !tab[r + 1][c]) || (c > 0 && !tab[r][c - 1]) || (c < 9 && !tab[r][c + 1]))) live++;
    if (live > 34) continue;
    const rows = tab.map(row => row.reduce((a, x, c) => a | (x ? 0 : 1 << c), 0));
    for (const o of ['V', 'H']) {
      sVal.fill(0); const a = resolverTab(tab, o), b = referencia(rows, o, new Map());
      if (a === b) ok++; else { mal++; console.log('DIVERGÊNCIA (referência) vez=' + o); }
    }
  }
  console.log(`Solver exato vs referência sem abstrações: ${ok} certos, ${mal} errados`);
  let ileg = 0, tot = 0, tmax = 0;
  const testes = [tabVazio()];
  for (let t = 0; t < 40; t++) {
    const tab = tabVazio(); abertura(rng, Math.floor(rng() * 30)).forEach((cs, i) => aplicar(tab, cs, i % 2 ? 'H' : 'V'));
    testes.push(tab);
  }
  for (const tab of testes) for (const o of ['V', 'H']) {
    if (listar(tab, o).length === 0) continue;
    const t0 = Date.now(); const cs = escolherJogada(tab, o, { tempoMs: 500, rng }); const dt = Date.now() - t0;
    tmax = Math.max(tmax, dt); tot++; if (!valida(tab, o, cs)) ileg++;
  }
  console.log(`Legalidade: ${tot - ileg}/${tot} jogadas legais; tempo máximo ${tmax} ms (limite 500)`);
}
function treinar(args) {
  const get = (k, d) => { const i = args.indexOf(k); return i >= 0 && i + 1 < args.length ? args[i + 1] : d; };
  const iters = +get('--iter', 60), tempo = +get('--tempo', 100), contra = get('--contra', null);
  const rng = mulberry32(+get('--seed', 1));
  const C = [20, 0.08, 0.08, 0.1, 0.1], lr = 0.25, theta = P.slice();
  const lim = (v, i) => i === 0 ? Math.max(10, v) : Math.min(0.9, Math.max(0, v));
  const opp = contra ? require(require('path').resolve(contra)).escolherJogada : null;
  const bot = w => (tab, o, opc) => { const sv = P; P = w; try { return escolherJogada(tab, o, opc); } finally { P = sv; } };
  for (let it = 1; it <= iters; it++) {
    const d = theta.map(() => (rng() < 0.5 ? -1 : 1));
    const bp = bot(theta.map((v, i) => lim(v + C[i] * d[i], i))), bm = bot(theta.map((v, i) => lim(v - C[i] * d[i], i)));
    const ab = abertura(rng, 1 + Math.floor(rng() * 3));
    let diff;
    if (!opp) diff = (jogarPartida(bp, bm, tempo, rng, ab) === 'V' ? 1 : -1) + (jogarPartida(bm, bp, tempo, rng, ab) === 'H' ? 1 : -1);
    else {
      const pts = b => (jogarPartida(b, opp, tempo, rng, ab) === 'V' ? 1 : 0) + (jogarPartida(opp, b, tempo, rng, ab) === 'H' ? 1 : 0);
      diff = pts(bp) - pts(bm);
    }
    for (let i = 0; i < theta.length; i++) theta[i] = lim(theta[i] + lr * diff * d[i] * C[i], i);
    if (it % 10 === 0 || it === iters) console.log(`iter ${it}  P = [${theta.map(v => +v.toFixed(3)).join(', ')}]`);
  }
  console.log('\nCola esta linha no topo do ficheiro:\nlet P = [' + theta.map(v => +v.toFixed(3)).join(', ') + '];');
}
if (require.main === module) {
  const args = process.argv.slice(2);
  if (args.includes('--verificar')) verificar();
  else if (args.includes('--treinar')) treinar(args);
  else console.log('Uso: node bot_novo.js --verificar | --treinar [--iter N] [--tempo ms] [--contra bot.js] [--seed n]');
}
