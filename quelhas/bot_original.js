'use strict';
/*
 * bot_novo.js — bot de Quelhas (10x10, misère: quem faz a última jogada PERDE).
 * Interface: module.exports = { escolherJogada(tab, orient, opc) }
 *
 * Modos extra (correr diretamente):
 *   node bot_novo.js --verificar
 *       compara o solver exato com força bruta e testa a legalidade e o tempo das jogadas
 *   node bot_novo.js --treinar [--iter 200] [--tempo 40] [--contra outro_bot.js] [--seed 1]
 *       afina os pesos W por SPSA (auto-jogo ou contra outro bot) e imprime a linha para colar abaixo
 *
 * Teorema usado (exato): se não há nenhuma casa disputada (livre e utilizável por V e por H ao mesmo tempo),
 * quem tem a vez ganha sse o seu número de runs (troços livres >=2) for <= ao do adversário.
 */

// ---------- Pesos da avaliação (perspetiva de quem tem a vez) ----------
// [0] runs exclusivas (adv - minhas)    [1] runs disputadas (adv - minhas)
// [2] mobilidade (minhas - adv)         [3] bónus de ter a vez
// [4] tempos de reserva nas runs exclusivas (minhas - adv)
let W = [100, 40, 0.5, 50, 12];

const EXACT_LIVE = 44;            // tenta solver exato com <= casas vivas
const FULL = 0x3FF;
const WIN = 1000000, MATE_TH = WIN - 1000, INF = 2000000000;
const EXACT = 1, LOWER = 2, UPPER = 3;
const ABORT = { abort: true };

// ---------- Tabelas por máscara de 10 bits ----------
const SEGS = new Array(1024), RUNS = new Array(1024);
const NSEG = new Uint8Array(1024), NRUN = new Uint8Array(1024);
const POPC = new Uint8Array(1024), CTZ = new Int8Array(1024);
(function () {
  for (let m = 0; m < 1024; m++) {
    let p = 0; for (let b = 0; b < 10; b++) if ((m >> b) & 1) p++;
    POPC[m] = p;
    CTZ[m] = m ? 31 - Math.clz32(m & -m) : -1;
    const segs = [], runs = [];
    let i = 0;
    while (i < 10) {
      if (!((m >> i) & 1)) { i++; continue; }
      let j = i; while (j < 10 && ((m >> j) & 1)) j++;
      const L = j - i;
      if (L >= 2) {
        runs.push(((1 << L) - 1) << i);
        for (let s = i; s <= j - 2; s++) for (let l = 2; s + l <= j; l++) segs.push((s << 4) | l);
      }
      i = j;
    }
    SEGS[m] = Int16Array.from(segs); NSEG[m] = segs.length;
    RUNS[m] = Int16Array.from(runs); NRUN[m] = runs.length;
  }
})();

// ---------- Zobrist ----------
let zs = 0x2545F491;
function zr() { zs ^= zs << 13; zs ^= zs >>> 17; zs ^= zs << 5; return zs | 0; }
const ZA = new Int32Array(100), ZB = new Int32Array(100);
for (let i = 0; i < 100; i++) { ZA[i] = zr(); ZB[i] = zr(); }
const SA = zr(), SB = zr();

// ---------- Estado (bitboards: linhas e colunas) ----------
const rowM = new Int32Array(10), colM = new Int32Array(10);
let h1 = 0, h2 = 0, side = 0;          // side 0 = V, 1 = H
let deadline = 0, nodes = 0, probeExact = true;

// ---------- Tabelas de transposição ----------
let TSIZE, TMASK, tKey, tScore, tMove, tDepth, tFlag;
function resizeTT(bits) {
  TSIZE = 1 << bits; TMASK = TSIZE - 1;
  tKey = new Int32Array(TSIZE); tScore = new Int32Array(TSIZE); tMove = new Int16Array(TSIZE);
  tDepth = new Int8Array(TSIZE); tFlag = new Uint8Array(TSIZE);
}
resizeTT(20);
const EBITS = 21, EMASK = (1 << EBITS) - 1;
const eKey = new Int32Array(1 << EBITS), eVal = new Uint8Array(1 << EBITS); // 1 ganha, 2 perde (quem tem a vez)
const HIST = new Int32Array(8192), K1 = new Int32Array(128), K2 = new Int32Array(128);
const MB = []; for (let i = 0; i < 128; i++) MB.push(new Int32Array(512));
function limparTT() { tKey.fill(0); tFlag.fill(0); HIST.fill(0); }

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

// ---------- Características ----------
const vuCol = new Int32Array(10), huRow = new Int32Array(10), contCol = new Int32Array(10), contRow = new Int32Array(10);
let fRv = 0, fRh = 0, fSv = 0, fSh = 0, fMv = 0, fMh = 0, fXv = 0, fXh = 0, fCont = 0, fLive = 0;
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
  let R = 0, S = 0, M = 0, X = 0;
  for (let c = 0; c < 10; c++) {
    const m = colM[c]; live += POPC[vuCol[c]]; M += NSEG[m]; const k = NRUN[m];
    if (k) {
      R += k; const rm = RUNS[m], cc = contCol[c];
      for (let j = 0; j < k; j++) { const run = rm[j]; if ((run & cc) === 0) { S++; X += (POPC[run] >> 1) - 1; } }
    }
  }
  fRv = R; fSv = S; fMv = M; fXv = X;
  R = 0; S = 0; M = 0; X = 0;
  for (let r = 0; r < 10; r++) {
    const m = rowM[r]; M += NSEG[m]; const k = NRUN[m];
    if (k) {
      R += k; const rm = RUNS[m], cc = contRow[r];
      for (let j = 0; j < k; j++) { const run = rm[j]; if ((run & cc) === 0) { S++; X += (POPC[run] >> 1) - 1; } }
    }
  }
  fRh = R; fSh = S; fMh = M; fXh = X; fCont = cont; fLive = live - cont;
}
function avaliar() {
  let Rme, Rop, Sme, Sop, Mme, Mop, Xme, Xop;
  if (side === 0) { Rme = fRv; Rop = fRh; Sme = fSv; Sop = fSh; Mme = fMv; Mop = fMh; Xme = fXv; Xop = fXh; }
  else { Rme = fRh; Rop = fRv; Sme = fSh; Sop = fSv; Mme = fMh; Mop = fMv; Xme = fXh; Xop = fXv; }
  return Math.round(W[0] * (Sop - Sme) + W[1] * ((Rop - Sop) - (Rme - Sme)) + W[2] * (Mme - Mop) + W[3] + W[4] * (Xme - Xop));
}

// ---------- Geração de jogadas (com eliminação de jogadas equivalentes em runs exclusivas) ----------
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
// Ordenação rápida: partir runs do adversário (+), não criar runs minhas (-)
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
function ordenarSimples(buf, n) {
  for (let i = 0; i < n; i++) { const mv = buf[i]; buf[i] = ((rapido(mv) * 16 + (mv & 15) + 131072) << 13) | mv; }
  buf.subarray(0, n).sort();
}

// ---------- Solver exato (booleano) ----------
function solveWin(ply) {
  if ((++nodes & 255) === 0 && Date.now() >= deadline) throw ABORT;
  const ei = h1 & EMASK;
  if (eVal[ei] !== 0 && eKey[ei] === h2) return eVal[ei] === 1;
  features();
  const Mme = side === 0 ? fMv : fMh;
  if (Mme === 0) return true;                         // sem jogada na minha vez: ganho
  if (fCont === 0) return (side === 0 ? fRv : fRh) <= (side === 0 ? fRh : fRv);
  const buf = MB[ply], n = gerar(buf);
  ordenarSimples(buf, n);
  let win = false;
  for (let i = n - 1; i >= 0; i--) {
    const mv = buf[i] & 8191;
    make(mv); const w = solveWin(ply + 1); unmake(mv);
    if (!w) { win = true; break; }
  }
  eKey[ei] = h2; eVal[ei] = win ? 1 : 2;
  return win;
}
function raizExata() {
  features(); const buf = MB[0], n = gerar(buf);
  ordenarSimples(buf, n);
  for (let i = n - 1; i >= 0; i--) {
    const mv = buf[i] & 8191;
    make(mv); const w = solveWin(1); unmake(mv);
    if (!w) return mv;
  }
  return -1;
}

// ---------- Alfa-beta (negamax PVS + TT + killers + history + LMR) ----------
function search(depth, alpha, beta, ply) {
  if ((++nodes & 255) === 0 && Date.now() >= deadline) throw ABORT;
  features();
  const Mme = side === 0 ? fMv : fMh;
  if (Mme === 0) return WIN - ply;
  if (fCont === 0) {
    const Rme = side === 0 ? fRv : fRh, Rop = side === 0 ? fRh : fRv;
    return Rme <= Rop ? WIN - (ply + 2 * Rme) : -(WIN - (ply + 2 * Rop + 1));
  }
  if (probeExact) {
    const ei = h1 & EMASK;
    if (eVal[ei] !== 0 && eKey[ei] === h2) return eVal[ei] === 1 ? WIN - ply - 100 : -(WIN - ply - 100);
  }
  if (depth <= 0) return avaliar();

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

function pensar(raiz, t0, budget, rng) {
  const ord = raiz.map(mv => ({ mv, sc: rapido(mv) * 100 + (mv & 15) * 3 + Math.floor(rng() * 40) }));
  ord.sort((a, b) => b.sc - a.sc);
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
      return best;
    }
    best = cur;
    ord.sort((a, b) => ((b.mv === cur) - (a.mv === cur)) || (b.sc - a.sc));
    if (curSc > MATE_TH || curSc < -MATE_TH) break;
    if (Date.now() - t0 > budget * 0.45) break;
  }
  return best;
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
function escolherJogada(tab, orient, opc) {
  const t0 = Date.now();
  opc = opc || {};
  const tempo = (typeof opc.tempoMs === 'number' && opc.tempoMs > 0) ? opc.tempoMs : 500;
  const rng = typeof opc.rng === 'function' ? opc.rng : Math.random;
  const budget = Math.max(10, Math.min(tempo * 0.8, tempo - 90));
  let res;
  try {
    for (let i = 0; i < 8192; i++) HIST[i] >>= 1;
    K1.fill(0); K2.fill(0); nodes = 0;
    setup(tab, orient);
    features();
    const n0 = gerar(MB[0]);
    if (n0 === 0) return [];
    const raiz = Array.from(MB[0].subarray(0, n0));
    if (raiz.length === 1) res = casas(raiz[0]);
    else {
      probeExact = true;
      let mv = 0;
      if (fLive <= EXACT_LIVE) {
        deadline = t0 + budget * (fLive <= 30 ? 0.65 : 0.35);
        try {
          const r = raizExata();
          if (r > 0) mv = r; else probeExact = false;   // perdido: joga pela heurística
        } catch (e) { if (e !== ABORT) throw e; setup(tab, orient); }
      }
      if (!mv) { deadline = t0 + budget; mv = pensar(raiz, t0, budget, rng); }
      res = casas(mv);
    }
  } catch (e) { res = null; }
  if (!valida(tab, orient, res)) res = reserva(tab, orient);
  return res;
}

module.exports = { escolherJogada };

// ---------- Modos de verificação e treino ----------
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
function posAleatoria(rng, grande) {
  const tab = tabVazio();
  if (!grande) {
    const p = 0.7 + rng() * 0.15;
    for (let r = 0; r < 10; r++) for (let c = 0; c < 10; c++) if (rng() < p) tab[r][c] = rng() < 0.5 ? 1 : 2;
    return tab;
  }
  for (const cs of [...abertura(rng, Math.floor(rng() * 30))].map((cs, i) => [cs, i])) aplicar(tab, cs[0], cs[1] % 2 ? 'H' : 'V');
  return tab;
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
function verificar() {
  const rng = mulberry32(7); let ok = 0, mal = 0;
  for (let t = 0; t < 400; t++) {
    const tab = posAleatoria(rng, false);
    for (const o of ['V', 'H']) {
      setup(tab, o); deadline = Infinity;
      const a = solveWin(0);
      setup(tab, o); const b = forcaBruta(new Map());
      if (a === b) ok++;
      else { mal++; if (mal <= 3) { console.log('DIVERGÊNCIA vez=' + o, 'solver=' + a, 'bruta=' + b); console.log(tab.map(r => r.join('')).join('\n')); } }
    }
  }
  console.log(`Solver exato vs força bruta: ${ok} certos, ${mal} errados`);
  let ileg = 0, tot = 0, tmax = 0;
  const testes = [tabVazio()];
  for (let t = 0; t < 40; t++) testes.push(posAleatoria(rng, true));
  for (const tab of testes) for (const o of ['V', 'H']) {
    if (listar(tab, o).length === 0) continue;
    const t0 = Date.now(); const cs = escolherJogada(tab, o, { tempoMs: 500, rng }); const dt = Date.now() - t0;
    tmax = Math.max(tmax, dt); tot++; if (!valida(tab, o, cs)) ileg++;
  }
  console.log(`Legalidade: ${tot - ileg}/${tot} jogadas legais; tempo máximo ${tmax} ms (limite 500)`);
}
function treinar(args) {
  const get = (k, d) => { const i = args.indexOf(k); return i >= 0 && i + 1 < args.length ? args[i + 1] : d; };
  const iters = +get('--iter', 200), tempo = +get('--tempo', 40), contra = get('--contra', null);
  const rng = mulberry32(+get('--seed', 1));
  resizeTT(16);
  const C = [20, 10, 0.25, 15, 6], lr = 0.25, theta = W.slice();
  const opp = contra ? require(require('path').resolve(contra)).escolherJogada : null;
  const bot = w => (tab, o, opc) => { const sv = W; W = w; limparTT(); try { return escolherJogada(tab, o, opc); } finally { W = sv; } };
  let saldo = 0;
  for (let it = 1; it <= iters; it++) {
    const d = theta.map(() => (rng() < 0.5 ? -1 : 1));
    const bp = bot(theta.map((v, i) => v + C[i] * d[i])), bm = bot(theta.map((v, i) => v - C[i] * d[i]));
    const ab = abertura(rng, 2 + Math.floor(rng() * 4));
    let diff;
    if (!opp) {
      diff = (jogarPartida(bp, bm, tempo, rng, ab) === 'V' ? 1 : -1) + (jogarPartida(bm, bp, tempo, rng, ab) === 'H' ? 1 : -1);
    } else {
      const pts = b => (jogarPartida(b, opp, tempo, rng, ab) === 'V' ? 1 : 0) + (jogarPartida(opp, b, tempo, rng, ab) === 'H' ? 1 : 0);
      diff = pts(bp) - pts(bm);
    }
    for (let i = 0; i < theta.length; i++) theta[i] += lr * diff * d[i] * C[i];
    saldo += diff;
    if (it % 10 === 0 || it === iters) console.log(`iter ${it}  W = [${theta.map(v => +v.toFixed(2)).join(', ')}]`);
  }
  console.log('\nCola esta linha no topo do ficheiro:\nlet W = [' + theta.map(v => +v.toFixed(2)).join(', ') + '];');
}
if (require.main === module) {
  const args = process.argv.slice(2);
  if (args.includes('--verificar')) verificar();
  else if (args.includes('--treinar')) treinar(args);
  else console.log('Uso: node bot_novo.js --verificar | --treinar [--iter N] [--tempo ms] [--contra bot.js] [--seed n]');
}
