'use strict';
/*
 * bot_novo.js — bot de Quelhas (10x10, misère: quem faz a última jogada PERDE).
 * Interface: module.exports = { escolherJogada(tab, orient, opc) }
 *
 * Como decide uma jogada (opc.tempoMs é limite duro; usa no máximo min(0.8*tempo, tempo-90) ms):
 *   1. livro de aberturas (V abre com a coluna 4 inteira; 2.ª jogada de V calculada com 12 s para cada
 *      resposta de H), consultado nas 4 simetrias que preservam V/H;
 *   2. se a posição já foi provada ganha numa jogada anterior (TT do solver), recupera a jogada da prova;
 *   3. alfa-beta (PVS + TT + killers + history) com avaliação aprendida, para ordenar as jogadas da raiz;
 *   4. verificação exata das melhores jogadas pelo solver por regiões, em rondas com top-K e orçamento
 *      de nós crescentes: joga uma vitória provada, nunca joga uma jogada provada perdedora se houver outra;
 *      se todas perdem, escolhe a de refutação mais cara.
 *
 * Solver exato: o tabuleiro decompõe-se em regiões independentes (componentes 4-conexas de casas livres).
 * Uma região em linha reta só serve a um jogador (run exclusiva) e resume-se à sua classe floor(L/2)-1
 * (jogadas de espera que permite): bastam 2 jogadas por jogador nessas runs (fechar a de menor classe,
 * encurtar em 2 a de menor classe >= 1). As outras regiões ficam num pool imutável; uma jogada só
 * recalcula a região onde foi feita. Chave da TT: soma dos hashes canónicos das regiões (invariantes por
 * translação e pelas 2 reflexões que preservam V/H; com H a jogar usa-se a transposta) + contadores.
 * TT com baldes de 2 entradas (a mais trabalhosa fica), persistente entre jogadas.
 *
 * Avaliação: rede 148-8-1 sobre 44 características globais (runs exclusivas/disputadas por classe,
 * mobilidade, casas disputadas e privadas, runs partíveis...) + 88 classes de padrões 3x3, treinada com
 * rótulos do solver exato e, nas posições anteriores ao 1.º ponto provado, com o valor desse ponto,
 * em 3 gerações de auto-jogo (ver ferramentas/).
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
const PIDX = new Int16Array(100), HACC = new Float64Array(64);
function avaliarML(R, C) {
  const ng = globais(R, C);
  let np = 0;
  for (let r = 1; r <= 10; r++) {
    let f = Rp[r];
    if (!f) continue;
    const up2 = Rp[r - 1] << 1, md2 = f << 1, dn2 = Rp[r + 1] << 1;
    while (f) {
      const b = f & -f; f ^= b; const c = CTZ[b], x = (md2 >> c) & 7;
      PIDX[np++] = PAT[((up2 >> c) & 7) | ((x & 1) << 3) | ((x >> 2) << 4) | (((dn2 >> c) & 7) << 5)];
    }
  }
  if (MOD_HID === 0) {
    let z = MOD_B;
    for (let j = 0; j < ng; j++) z += MOD_WG[j] * G[j];
    for (let k = 0; k < np; k++) z += MOD_WP[PIDX[k]];
    return z;
  }
  let z = MOD_B;
  for (let h = 0; h < MOD_HID; h++) {
    let a = MOD_B1[h]; const og = h * NG, op = h * NPAT;
    for (let j = 0; j < ng; j++) a += MOD_WG[og + j] * G[j];
    for (let k = 0; k < np; k++) a += MOD_WP[op + PIDX[k]];
    z += MOD_W2[h] * (a > 0 ? a : 0.01 * a);
  }
  return z;
}
// @@MODELO@@
const MODELO_EMB = { HID: 8, WG: [-0.10952,-0.17956,-0.041363,-0.00031809,0.0070657,-0.24711,-1.9854,-0.41307,-0.19271,-0.25569,0.58753,-0.31945,0.092394,-0.029649,0.71099,-0.024671,-0.27774,0.088644,0.38426,-0.008509,-0.12647,0.086909,-0.56545,-0.0051856,-0.25879,0.048904,-1.0654,-0.46512,-0.43398,0.23909,-0.074801,-0.011291,0.082258,-1.3184,-0.42218,0.42795,-0.29108,-0.06109,0.12448,0.042764,0.2916,0.4757,0.075829,-2.1005,1.2418e-305,-3.9541e-304,7.4088e-304,2.1939e-306,1.0557e-304,-8.5015e-304,-8.3277e-305,4.6803e-304,4.5017e-304,-4.8083e-304,-7.8082e-305,-2.4441e-304,2.2879e-303,3.2222e-304,-8.6346e-303,-1.0247e-303,-2.2794e-304,-1.3724e-304,-1.3065e-304,2.3045e-306,-0.42654,-0.1757,0.027124,-0.032411,-0.12876,0.11802,-0.6954,0.57093,-0.042006,-0.1207,0.23674,-0.26012,0.032007,0.12329,0.54474,-0.62996,0.0056511,-0.030302,0.038133,0.01155,0.11784,-0.26294,-0.82132,-0.83658,-0.025712,-0.009099,-0.91119,0.11519,-0.033172,-0.11508,0.020661,-0.000536,-0.73835,0.7885,-0.089385,-0.95684,0.25505,0.013952,0.014883,0.0028281,-0.99368,-0.79746,0.33728,-0.38007,3.2235e-304,-2.6373e-304,2.1133e-303,7.5208e-304,3.0984e-304,-1.3627e-304,2.8341e-303,3.0984e-303,3.1081e-304,-4.1661e-303,4.1377e-304,4.3836e-304,2.5833e-305,-1.5261e-303,5.0303e-303,1.4972e-304,4.4504e-303,1.4901e-304,-4.0357e-303,5.4908e-304,0.17619,0.12132,0.0036429,0.031992,-0.010739,0.041903,-0.42837,0.43469,0.28366,0.26947,0.11555,-0.11589,0.018809,0.031754,-0.99671,0.48243,-0.050418,0.027778,-0.4477,-0.86123,0.11555,0.11753,-0.4943,0.25014,0.11487,-0.014855,-0.11435,-2.4243,-0.083897,-0.40695,0.035275,-0.03426,-0.46041,0.71704,0.36276,-0.22267,0.11638,-0.23166,-0.027363,0.028518,0.38615,0.33502,-0.29233,-0.035484,1.045e-304,1.1116e-303,7.2075e-304,3.0104e-303,2.6176e-304,1.2255e-303,-3.1061e-304,-3.7195e-304,5.098e-305,1.0571e-304,1.2309e-304,-3.5242e-303,6.3013e-305,7.9831e-305,4.1775e-304,3.7856e-304,-3.9069e-304,5.6156e-303,-1.9565e-304,-2.5092e-304,0.33828,0.089854,0.0032047,0.093348,0.029799,-0.075289,-0.54662,0.79302,0.046317,-0.15183,-0.65333,0.42651,-0.00022296,0.024323,-0.4505,0.042174,0.019717,0.026673,-0.17084,-0.61981,-0.019084,-0.080287,0.22013,-0.56041,0.035531,-0.072631,-0.46109,-1.0926,0.10382,-0.16169,0.0055002,-0.01087,-0.40864,1.379,0.24382,-0.50599,0.18024,-0.093852,0.037294,-0.030099,0.51833,0.36835,-0.88709,-7.2942,-7.1326e-306,-5.1416e-304,3.9697e-307,1.6237e-304,-3.6182e-304,-1.5287e-304,-1.9059e-305,-4.5375e-303,-2.4241e-304,-3.1171e-304,1.1602e-303,4.3839e-305,2.8588e-305,7.7796e-305,-2.2151e-304,4.5503e-304,9.1803e-303,2.7168e-304,5.6074e-305,5.8727e-305,0.53583,-0.46789,0.0090326,0.010572,-0.10389,-0.010621,-0.68931,-0.4295,-0.065973,0.0053919,0.60568,-0.85799,0.059603,-0.0096262,0.56735,-0.206,-0.02917,-0.0032791,-0.15346,-0.33477,-0.09744,0.11404,0.072244,-0.20178,-0.27131,0.14319,-1.583,-0.1132,-0.59698,0.14861,-0.027904,-0.0061903,-0.71186,-0.83933,-0.42693,0.30046,-0.22688,0.21161,0.031198,0.04828,0.65975,0.52841,-0.45015,-1.6201,-5.9511e-305,2.2157e-304,1.0173e-304,-1.1801e-303,-3.0746e-305,-5.9044e-306,-1.8278e-303,-3.8847e-304,2.1004e-304,-2.6031e-304,-9.5986e-305,-3.2975e-303,2.264e-304,9.9237e-304,-5.4536e-306,-1.341e-306,2.5577e-304,-4.2067e-305,3.0992e-304,-5.3659e-304,-0.03772,0.24261,-0.063107,0.11505,0.034234,0.085017,-0.92234,-0.48999,0.0936,0.052427,1.0399,0.42407,0.10919,0.02409,-0.43896,0.54679,-0.013035,0.027703,-0.83932,-0.16933,-0.26429,-0.023826,-2.5969,0.29952,-0.062953,0.04639,0.35715,-1.2949,-0.29563,0.021931,-0.060133,-0.0059415,1.0228,-0.71969,-1.0072,-0.017311,-0.10433,0.18176,0.011579,0.036713,0.47796,0.39169,-0.61257,-0.23713,8.4608e-305,-1.3158e-304,2.6426e-304,-8.6871e-305,6.1748e-304,6.2294e-304,1.2961e-303,-8.0463e-304,1.482e-303,2.536e-304,6.482e-307,6.7342e-305,6.2964e-304,-3.1547e-305,-1.216e-306,1.5353e-303,3.4464e-304,8.0187e-305,4.3048e-304,3.5162e-304,-0.42514,-0.16363,0.054793,0.033026,-0.048962,-0.050934,0.72006,0.17535,0.07025,0.16761,0.37066,0.37086,-0.036494,0.074132,0.30149,-0.24012,0.1757,-0.10402,-0.239,-0.29245,0.10036,0.069192,0.18432,-1.2039,0.23198,-0.29967,0.36948,-0.53622,-0.22005,-0.34241,0.019654,-0.0063901,-0.80369,0.6807,0.27427,-0.20803,0.2262,-0.17979,0.056059,0.045692,0.38344,0.24907,-0.21798,-0.6479,-4.5174e-304,-1.0762e-303,1.3009e-305,-1.3218e-304,2.9521e-303,-2.0882e-304,2.7039e-304,2.3498e-305,-3.8562e-305,3.4888e-304,2.2855e-305,1.288e-304,1.8833e-303,-5.886e-305,2.3805e-305,2.1185e-303,-4.5298e-306,4.1094e-306,9.8887e-304,4.6107e-305,0.30681,0.017384,0.03355,0.092499,0.035947,-0.045313,-0.64366,0.42255,0.1128,0.21612,-0.41678,0.081832,-0.015911,0.077538,0.15756,0.62515,0.048708,-0.084077,0.0047193,0.33068,0.27357,-0.067051,0.22443,-0.28079,0.077157,-0.17086,-0.27909,-1.9228,0.057524,-0.3604,0.056926,-0.017285,-0.11152,1.0867,0.24509,-0.10985,0.22556,-0.32292,0.058717,0.072329,0.19279,0.23536,-0.052961,-0.74636,-8.6023e-304,4.0711e-303,1.2544e-305,2.0324e-303,-6.7816e-306,-1.5198e-305,1.4018e-305,-2.0091e-303,1.1316e-304,4.2957e-304,5.0314e-304,-1.6119e-304,-1.611e-304,-2.9792e-304,1.0592e-303,-4.3608e-304,8.126e-304,1.133e-303,7.4074e-304,6.8466e-304], WP: [1.0365,-0.61544,0.087155,0.02317,3.315,-0.20548,-0.057509,-0.92945,-0.1965,0.038431,0.22213,-0.81001,1.0605,-0.55644,0.04606,0.054051,0.39874,-0.26597,-0.4787,0.012931,1.6488,0.052126,-0.46695,5.4224e-305,6.8675e-307,3.0122,-0.94871,0.55015,1.3495,-0.18316,2.7513,0.45313,2.3507,1.0424,9.5926,-0.86775,-3.1903,2.1721,0.032794,-0.60173,0.38749,3.656,-0.5,3.2522,0.030767,-0.14201,-0.52394,-0.090371,-0.27213,5.0842,0.7617,0.26906,-0.25011,3.1128,0.41742,-1.5367,1.9039e-306,1.3308,5.6984,1.4067,-0.45268,2.0666,-0.5335,0.57648,-0.049948,0.10608,-1.5573,-0.2861,1.2691,5.6278,1.0077,-0.60042,-0.80527,1.5771,-0.24906,-5.3931e-305,2.3907,3.0635,0.21016,6.7358,0.32659,-1.9514,-0.29791,-0.010567,-0.83063,-0.61737,-0.052493,-0.26841,0.058637,-0.34521,-0.033267,-0.089608,-0.11762,0.064675,0.90707,0.32155,0.86947,0.014764,-0.17466,-0.25274,-0.20994,-0.12613,-0.12774,-0.043682,7.634,-0.61189,-0.60616,4.6736e-305,3.3706e-304,0.13726,2.5824,-1.033,1.9937,-0.18767,-3.3614,-1.4449,-4.2734,-0.14823,13.244,-2.6837,0.61507,-0.28354,0.25754,0.34549,0.68131,2.1905,0.3309,0.84269,-0.14734,-0.7713,-0.066044,0.015535,0.16469,6.5707,-0.50925,-0.16867,0.014108,-3.2668,1.2671,0.0081162,6.1873e-306,6.0632,4.2431,0.80707,0.17369,-0.15376,-1.1884,0.12033,-0.0059979,-0.13053,-0.85458,-0.079571,6.6317,2.6271,-0.12613,-0.26787,-0.38666,0.86731,-0.029132,-2.4677e-306,4.6645,6.8976,-0.69907,3.2543,0.19991,-4.6171,-0.2839,-0.0021411,-0.92708,0.5148,-0.079197,-0.52798,1.4115,0.23443,0.11057,0.059035,-0.44838,0.01662,0.73734,0.22378,0.57041,0.46374,-0.11348,0.21713,1.0348,0.47937,-0.18726,0.017631,-3.4867,0.16625,0.5954,2.6981e-305,2.0355e-306,0.53825,0.55803,2.3913,0.043503,0.2026,4.8046,2.5949,-0.37742,1.2955,1.8489,2.0049,7.3571,2.0544,0.54573,0.25126,0.11903,1.3616,0.015871,1.1172,-0.80108,-0.64491,0.10759,0.089535,0.10975,-1.8572,1.61,-0.5406,0.14392,2.4395,-2.0171,0.79955,-1.3201e-306,1.5498,1.2089,-0.95487,-0.077025,-4.3506,-0.0076384,-0.17502,0.01621,1.641,0.085914,0.19337,-3.6102,-5.8751,-0.45674,0.83654,0.97979,0.53352,0.05554,4.0779e-305,-6.6265,-7.7511,0.59309,8.7542,0.16219,5.297,0.09101,-0.039659,0.81557,-0.35704,-0.053775,-0.086695,-0.44848,-0.70978,0.019777,0.00791,-0.06714,0.0076913,-0.018932,0.30076,-0.413,-0.063823,-0.072819,0.17991,-0.044002,0.071682,-0.15317,0.0011157,4.0477,0.2056,-0.48313,-9.9065e-305,-8.6183e-306,-0.35985,-2.0972,0.53368,-0.2637,0.35142,-6.7457,1.7738,0.45763,-0.4714,-14.374,0.74785,-10.437,1.7557,0.093624,-0.82916,0.19419,-2.3192,0.50962,-0.13932,0.80929,-0.064723,-0.070032,0.10174,0.043556,6.313,-0.239,-0.54889,0.0098615,-8.1721,-4.6351,0.00080532,-3.8229e-305,-7.7323,-10.596,0.74534,-0.098117,-1.5716,0.69772,-0.94194,0.022313,0.35849,0.47711,0.17135,-17.449,-9.6358,-0.17477,-0.92729,-0.020133,-0.26102,-0.010655,7.6053e-304,-3.6968,-13.361,-0.20965,-18.548,-0.012941,-9.5643,-0.19272,-0.00032927,-0.59057,-0.98614,0.091812,-0.29508,-1.0734,1.3529,-0.22168,-0.028311,-0.2638,0.021445,-0.68938,0.25771,-1.0432,0.17455,0.10112,0.066513,-0.28988,0.22149,-0.092228,0.0023782,-13.262,-0.9064,0.088284,5.6374e-305,-1.7127e-305,-9.3262,0.10784,-0.73547,0.17653,0.3223,-0.85163,-11.253,-4.7409,0.17203,-18.647,1.2358,2.5099,1.7784,0.28635,0.45192,0.88089,-8.5076,-0.14716,-1.052,-0.050304,-0.11279,-0.054227,-0.066149,0.075492,6.5454,-0.09433,0.1414,0.35283,-16.11,1.7681,0.84056,2.3275e-305,1.4351,-14.503,0.18357,-0.32689,-0.28356,0.63705,-0.20243,0.013042,0.55382,0.76483,-0.044514,-13.854,-12.321,-1.1953,-0.94146,0.11256,0.26047,-0.035563,-1.0582e-305,-13.801,1.6242,0.14922,1.9795,0.12364,2.3417,-0.11063,-0.027971,-0.32383,-0.62538,-0.048083,-0.31603,-1.0278,-0.59169,-0.11028,-0.15895,-0.25791,0.079745,0.084137,-0.43479,1.8117,-0.16982,0.034895,0.12251,-0.63849,0.032107,-0.40831,0.015462,3.7751,1.5731,0.12884,4.4532e-305,-7.1461e-305,2.4191,0.65784,0.54037,1.5849,-0.16068,0.77702,4.6352,0.98949,0.36931,4.1094,0.0015179,3.8359,0.15238,0.34277,-0.97768,-0.38906,-0.064757,0.3168,-0.86853,0.84277,-1.2648,0.058035,-0.20238,-0.085188,1.9831,0.59258,-0.11955,-0.080764,3.4978,-1.8075,0.28361,-3.955e-305,2.3033,10.502,-0.34488,0.0039461,1.7575,2.5834,-0.1052,-0.035061,0.71217,-0.84233,0.070045,0.41254,-3.3676,2.0119,0.52366,-0.03923,0.8439,-0.001452,-2.3314e-305,2.7666,-1.1448,-1.0631,-1.4105,-0.34198,-4.1927,-0.088806,-0.024819,0.35407,-1.5928,0.023662,-0.50425,0.32876,3.0699,0.12989,0.094474,-0.18087,0.047112,0.37181,-0.55557,1.2273,-0.049243,-0.036906,-0.49328,-0.0036268,-0.30328,-0.083036,-0.020516,-3.0432,1.1504,-0.32122,-2.4267e-305,-6.3616e-305,-1.8781,-0.28521,-2.6206,0.10084,-0.45201,3.0601,-3.1371,2.2434,0.30248,17.735,0.5312,2.9191,2.8431,0.38206,-0.2845,0.33058,3.1423,-1.2033,1.1363,0.10623,0.22701,-0.043661,0.068631,-0.029866,9.4922,-0.12223,-0.33124,-0.17189,1.6474,-3.5053,0.64663,1.075e-304,-3.8047,-4.9703,0.36314,-0.30692,2.0312,1.2899,0.68383,0.025259,-0.32875,-0.1356,-0.36356,6.2764,-0.11166,0.36422,0.35214,-0.19855,-0.066796,-0.18346,1.9067e-308,4.254,-2.6058,1.2181,-2.5088,-0.46607,0.061573,0.066753,-0.00012386,0.54602,-0.36194,-0.0054721,-0.080468,0.82856,-1.4009,0.087587,-0.42263,-0.31815,0.026943,-1.7545,-0.91597,0.41915,-0.3289,-0.037716,-0.048894,0.84505,0.030476,-0.55747,-0.017226,-4.4587,-0.83344,0.052857,1.2194e-305,-6.1023e-306,4.0301,-2.985,-2.4788,0.69972,-0.066511,-1.8287,1.173,0.80539,1.2247,-6.9329,-2.622,-6.545,0.95293,-0.5757,0.3308,0.58263,1.024,-0.32347,-0.34984,-0.27657,-1.0916,-0.051989,0.061387,-0.026647,3.5133,-0.27777,-0.10438,0.16991,6.5981,2.6046,-0.81998,2.1175e-305,3.2625,5.0224,-0.82767,-0.51258,1.6939,1.6312,0.071459,0.025669,-2.6942,-0.59771,-0.30177,2.047,1.268,0.91708,-0.067718,0.60734,1.3333,-0.2229,-3.4621e-304,-7.327,2.3966,-3.386,0.087135,-0.15159,-4.3474,0.22966,-0.034661], B1: [5.8823,1.5606,-0.42647,1.273,0.61328,0.47313,-0.95365,2.0518], W2: [-0.72648,0.77084,0.49494,0.71452,-0.7858,-0.74924,0.82152,0.56639], B2: -0.13608 };
// @@FIM_MODELO@@
const MOD_HID = MODELO_EMB.HID, MOD_B = MODELO_EMB.B2, MOD_WG = Float64Array.from(MODELO_EMB.WG), MOD_WP = Float64Array.from(MODELO_EMB.WP);
const MOD_B1 = Float64Array.from(MODELO_EMB.B1), MOD_W2 = Float64Array.from(MODELO_EMB.W2);

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
function limparTT() { tKey.fill(0); tFlag.fill(0); HIST.fill(0); sVal.fill(0); sWork.fill(0); }

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
// valor da posição atual (rowM, side) na TT do solver: 1 ganha, 2 perde, 0 desconhecido (deixa o nível 0 carregado)
function raizNaTT() {
  carregarSolver();
  const n = NL[0], ME = side === 0 ? CNTV : CNTH, OP = side === 0 ? CNTH : CNTV;
  if (n === 0) return ME[0] + ME[1] + ME[2] + ME[3] + ME[4] <= OP[0] + OP[1] + OP[2] + OP[3] + OP[4] ? 1 : 2;
  let k1 = 0, k2 = 0; const ho = side === 0 ? 0 : 2;
  for (let i = 0; i < n; i++) { const id = LIST[i]; k1 = k1 + CH[id * 4 + ho] | 0; k2 = k2 + CH[id * 4 + ho + 1] | 0; }
  for (let i = 0; i < 5; i++) { const a = ME[i], b = OP[i]; k1 = k1 + Math.imul(a, ZC1[i]) + Math.imul(b, ZC1[5 + i]) | 0; k2 = k2 + Math.imul(a, ZC2[i]) + Math.imul(b, ZC2[5 + i]) | 0; }
  const e0 = k1 & (SMASK - 1), tag = (k1 >>> 26) << 2;
  for (let e = e0; e <= e0 + 1; e++) { const ev = sVal[e]; if (ev !== 0 && sKey[e] === k2 && (ev & 0xFC) === tag) return ev & 3; }
  return 0;
}
// com a raiz já provada ganha: procura a jogada vencedora pela ordem do próprio solver (reaproveita a prova)
function jogadaDaProva(tFim, raiz) {
  deadline = tFim;
  const buf = SBUF[0], m = gerarSolver(0, side, buf);
  buf.subarray(0, m).sort();
  const mvs = []; for (let i = m - 1; i >= 0; i--) mvs.push(buf[i] & 0x3FFFF);
  const save = poolTop;
  try {
    for (const mv of mvs) {
      fazer(0, side, mv);
      const w = resolve(1, side ^ 1);
      poolTop = save;
      if (!w) return solverParaAB(mv, raiz);
    }
  } catch (e) { if (e !== ABORT) throw e; }
  return 0;
}
// jogada do solver (nível 0) -> jogada da alfa-beta (da lista raiz). As abstratas (fechar / encurtar uma run
// exclusiva da classe t) correspondem a qualquer jogada numa run exclusiva dessa classe que deixe as mesmas sobras.
function solverParaAB(mv, raiz) {
  if ((mv >>> 12) !== ABS) return (side << 12) | (mv & 4095);
  const t = (mv >> 8) & 15, enc = mv & 1, A = side === 0 ? colM : rowM;
  for (const x of raiz) {
    if ((x >> 12) !== side) continue;
    const line = (x >> 8) & 15, st = (x >> 4) & 15, l = x & 15, m = A[line];
    const nb = m & ((line > 0 ? A[line - 1] : 0) | (line < 9 ? A[line + 1] : 0)), rm = RUNS[m];
    for (let j = 0; j < rm.length; j++) {
      const run = rm[j], L = POPC[run], s0 = CTZ[run];
      if (st < s0 || st >= s0 + L) continue;
      if ((run & nb) !== 0 || (L >> 1) - 1 !== t) break;
      const ra = st - s0, rb = L - ra - l, ka = (ra >= 2 ? 1 : 0) + (rb >= 2 ? 1 : 0);
      if (!enc && ka === 0) return x;
      if (enc && ka === 1 && Math.max(ra, rb) === L - 2) return x;
      break;
    }
  }
  return 0;
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
const LIVRO = {
  '40f7ef7ef7ef7ef7ef7ef7ef7ef7efV': [0, 7, 1, 9],
  '42f7ef7ef7ef7ef7ef7ef7ef7ef7efV': [0, 7, 1, 9],
  '46f7ef7ef7ef7ef7ef7ef7ef7ef7efV': [0, 7, 1, 9],
  '4ef7ef7ef7ef7ef7ef7ef7ef7ef7efV': [0, 7, 0, 10],
  '60f7ef7ef7ef7ef7ef7ef7ef7ef7efV': [0, 7, 1, 9],
  '62f7ef7ef7ef7ef7ef7ef7ef7ef7efV': [0, 7, 1, 9],
  '66f7ef7ef7ef7ef7ef7ef7ef7ef7efV': [0, 7, 1, 9],
  '70f7ef7ef7ef7ef7ef7ef7ef7ef7efV': [0, 7, 1, 9],
  '72f7ef7ef7ef7ef7ef7ef7ef7ef7efV': [0, 7, 1, 9],
  '78f7ef7ef7ef7ef7ef7ef7ef7ef7efV': [0, 7, 0, 10],
  '7e07ef7ef7ef7ef7ef7ef7ef7ef7efV': [0, 6, 1, 8],
  '7e17ef7ef7ef7ef7ef7ef7ef7ef7efV': [0, 6, 1, 8],
  '7e37ef7ef7ef7ef7ef7ef7ef7ef7efV': [0, 8, 1, 8],
  '7e87ef7ef7ef7ef7ef7ef7ef7ef7efV': [0, 6, 0, 10],
  '7e97ef7ef7ef7ef7ef7ef7ef7ef7efV': [0, 6, 0, 10],
  '7ec7ef7ef7ef7ef7ef7ef7ef7ef7efV': [0, 6, 0, 10],
  '7ef40f7ef7ef7ef7ef7ef7ef7ef7efV': [0, 1, 0, 10],
  '7ef42f7ef7ef7ef7ef7ef7ef7ef7efV': [0, 6, 2, 8],
  '7ef46f7ef7ef7ef7ef7ef7ef7ef7efV': [0, 6, 0, 10],
  '7ef4ef7ef7ef7ef7ef7ef7ef7ef7efV': [0, 6, 0, 10],
  '7ef60f7ef7ef7ef7ef7ef7ef7ef7efV': [0, 8, 2, 8],
  '7ef62f7ef7ef7ef7ef7ef7ef7ef7efV': [0, 8, 2, 8],
  '7ef66f7ef7ef7ef7ef7ef7ef7ef7efV': [0, 6, 0, 10],
  '7ef70f7ef7ef7ef7ef7ef7ef7ef7efV': [0, 8, 0, 10],
  '7ef72f7ef7ef7ef7ef7ef7ef7ef7efV': [0, 8, 0, 10],
  '7ef78f7ef7ef7ef7ef7ef7ef7ef7efV': [0, 8, 0, 10],
  '7ef7e07ef7ef7ef7ef7ef7ef7ef7efV': [0, 8, 0, 10],
  '7ef7e17ef7ef7ef7ef7ef7ef7ef7efV': [0, 6, 0, 10],
  '7ef7e37ef7ef7ef7ef7ef7ef7ef7efV': [0, 8, 1, 8],
  '7ef7e87ef7ef7ef7ef7ef7ef7ef7efV': [0, 6, 0, 10],
  '7ef7e97ef7ef7ef7ef7ef7ef7ef7efV': [0, 6, 0, 10],
  '7ef7ec7ef7ef7ef7ef7ef7ef7ef7efV': [0, 8, 1, 8],
  '7ef7ef40f7ef7ef7ef7ef7ef7ef7efV': [0, 7, 3, 7],
  '7ef7ef42f7ef7ef7ef7ef7ef7ef7efV': [0, 6, 3, 7],
  '7ef7ef46f7ef7ef7ef7ef7ef7ef7efV': [0, 6, 0, 10],
  '7ef7ef4ef7ef7ef7ef7ef7ef7ef7efV': [0, 1, 0, 10],
  '7ef7ef60f7ef7ef7ef7ef7ef7ef7efV': [0, 8, 3, 7],
  '7ef7ef62f7ef7ef7ef7ef7ef7ef7efV': [0, 6, 3, 7],
  '7ef7ef66f7ef7ef7ef7ef7ef7ef7efV': [0, 2, 0, 10],
  '7ef7ef70f7ef7ef7ef7ef7ef7ef7efV': [0, 8, 0, 10],
  '7ef7ef72f7ef7ef7ef7ef7ef7ef7efV': [0, 2, 0, 10],
  '7ef7ef78f7ef7ef7ef7ef7ef7ef7efV': [0, 1, 0, 10],
  '7ef7ef7e07ef7ef7ef7ef7ef7ef7efV': [0, 6, 0, 10],
  '7ef7ef7e17ef7ef7ef7ef7ef7ef7efV': [0, 6, 0, 10],
  '7ef7ef7e37ef7ef7ef7ef7ef7ef7efV': [0, 6, 0, 10],
  '7ef7ef7e87ef7ef7ef7ef7ef7ef7efV': [0, 6, 0, 10],
  '7ef7ef7e97ef7ef7ef7ef7ef7ef7efV': [0, 8, 0, 10],
  '7ef7ef7ec7ef7ef7ef7ef7ef7ef7efV': [0, 8, 1, 8],
  '7ef7ef7ef40f7ef7ef7ef7ef7ef7efV': [0, 1, 0, 10],
  '7ef7ef7ef42f7ef7ef7ef7ef7ef7efV': [0, 1, 0, 10],
  '7ef7ef7ef46f7ef7ef7ef7ef7ef7efV': [0, 6, 0, 10],
  '7ef7ef7ef4ef7ef7ef7ef7ef7ef7efV': [0, 1, 0, 10],
  '7ef7ef7ef60f7ef7ef7ef7ef7ef7efV': [0, 1, 0, 10],
  '7ef7ef7ef62f7ef7ef7ef7ef7ef7efV': [0, 2, 0, 10],
  '7ef7ef7ef66f7ef7ef7ef7ef7ef7efV': [0, 2, 0, 10],
  '7ef7ef7ef70f7ef7ef7ef7ef7ef7efV': [0, 8, 0, 10],
  '7ef7ef7ef72f7ef7ef7ef7ef7ef7efV': [0, 2, 0, 10],
  '7ef7ef7ef78f7ef7ef7ef7ef7ef7efV': [0, 1, 0, 10],
  '7ef7ef7ef7e07ef7ef7ef7ef7ef7efV': [0, 8, 0, 10],
  '7ef7ef7ef7e17ef7ef7ef7ef7ef7efV': [0, 6, 0, 10],
  '7ef7ef7ef7e37ef7ef7ef7ef7ef7efV': [0, 6, 1, 8],
  '7ef7ef7ef7e87ef7ef7ef7ef7ef7efV': [0, 6, 0, 10],
  '7ef7ef7ef7e97ef7ef7ef7ef7ef7efV': [0, 6, 0, 10],
  '7ef7ef7ef7ec7ef7ef7ef7ef7ef7efV': [0, 8, 0, 10],
  '7ef7ef7ef7ef40f7ef7ef7ef7ef7efV': [0, 2, 0, 10],
  '7ef7ef7ef7ef42f7ef7ef7ef7ef7efV': [0, 1, 0, 10],
  '7ef7ef7ef7ef46f7ef7ef7ef7ef7efV': [0, 2, 0, 10],
  '7ef7ef7ef7ef4ef7ef7ef7ef7ef7efV': [0, 6, 0, 10],
  '7ef7ef7ef7ef60f7ef7ef7ef7ef7efV': [0, 1, 0, 10],
  '7ef7ef7ef7ef62f7ef7ef7ef7ef7efV': [0, 2, 0, 10],
  '7ef7ef7ef7ef66f7ef7ef7ef7ef7efV': [0, 1, 0, 10],
  '7ef7ef7ef7ef70f7ef7ef7ef7ef7efV': [0, 2, 0, 10],
  '7ef7ef7ef7ef72f7ef7ef7ef7ef7efV': [0, 2, 0, 10],
  '7ef7ef7ef7ef78f7ef7ef7ef7ef7efV': [0, 2, 0, 10],
  '7ef7ef7ef7ef7e07ef7ef7ef7ef7efV': [0, 8, 0, 10],
  '7ef7ef7ef7ef7e17ef7ef7ef7ef7efV': [0, 6, 0, 10],
  '7ef7ef7ef7ef7e37ef7ef7ef7ef7efV': [0, 8, 0, 10],
  '7ef7ef7ef7ef7e87ef7ef7ef7ef7efV': [0, 8, 0, 10],
  '7ef7ef7ef7ef7e97ef7ef7ef7ef7efV': [0, 6, 0, 10],
  '7ef7ef7ef7ef7ec7ef7ef7ef7ef7efV': [0, 6, 0, 10],
  '7ff7ff7ff7ff7ff7ff7ff7ff7ff7ffV': [0, 4, 0, 10],
};
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
      if (L <= 92 && raizNaTT() === 1) {        // já provada ganha (numa jogada anterior): recuperar a jogada
        const x = jogadaDaProva(t0 + budget * 0.6, raiz);
        if (x && raiz.indexOf(x) >= 0) { mv = x; ultimo.estado = 'ganha'; }
      }
    }
    if (!mv && raiz.length > 1) {
      const L = fLive;
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
