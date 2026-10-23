'use strict';
/*
 * arena.js — joga partidas de Quelhas entre dois bots, em vários processos.
 *
 *   node arena.js A.js B.js [--jogos 100] [--tempo 500] [--proc 4] [--abertura 0] [--seed 1] [--out f.jsonl]
 *
 * As partidas vão aos pares com a mesma abertura (A de V e depois A de H).
 * --abertura k joga k jogadas aleatórias antes de os bots começarem (0 = tabuleiro vazio).
 * Jogada ilegal, exceção ou tempo acima de --tempo (mais --folga ms) contam como derrota.
 */
const path = require('path');
const fs = require('fs');
const { fork } = require('child_process');

function mulberry32(a) {
  return function () {
    a |= 0; a = a + 0x6D2B79F5 | 0;
    let t = Math.imul(a ^ a >>> 15, 1 | a);
    t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t;
    return ((t ^ t >>> 14) >>> 0) / 4294967296;
  };
}
const tabVazio = () => [...Array(10)].map(() => Array(10).fill(0));
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
const aplicar = (tab, cs, o) => { for (const [r, c] of cs) tab[r][c] = o === 'V' ? 1 : 2; };
function abertura(rng, k) {
  const tab = tabVazio(), seq = []; let o = 'V';
  for (let i = 0; i < k; i++) {
    const L = listar(tab, o); if (!L.length) break;
    const cs = L[Math.floor(rng() * L.length)]; aplicar(tab, cs, o); seq.push(cs);
    o = o === 'V' ? 'H' : 'V';
  }
  return seq;
}

// ---------- worker ----------
function worker() {
  const [fa, fb, tempo, folga, tA, tB] = JSON.parse(process.env.ARENA_CFG);
  const A = require(path.resolve(fa)).escolherJogada, B = require(path.resolve(fb)).escolherJogada;
  process.on('message', job => {
    if (job === 'fim') process.exit(0);
    const { id, ab, aEhV, seed } = job;
    const rng = mulberry32(seed);
    const tab = tabVazio(); let o = 'V';
    const jogadas = [];
    for (const cs of ab) { aplicar(tab, cs, o); jogadas.push(cs); o = o === 'V' ? 'H' : 'V'; }
    let vencedor = null, motivo = 'normal', tmax = { A: 0, B: 0 };
    for (let k = 0; k < 200 && !vencedor; k++) {
      if (listar(tab, o).length === 0) { vencedor = o; break; }
      const quem = (o === 'V') === aEhV ? 'A' : 'B';
      const bot = quem === 'A' ? A : B;
      const t0 = process.hrtime.bigint(); let cs;
      const tq = quem === 'A' ? (tA || tempo) : (tB || tempo);
      try { cs = bot(tab.map(r => r.slice()), o, { tempoMs: tq, rng }); } catch (e) { cs = null; motivo = 'excecao:' + e.message; }
      const dt = Number(process.hrtime.bigint() - t0) / 1e6;
      if (dt > tmax[quem]) tmax[quem] = dt;
      const outro = o === 'V' ? 'H' : 'V';
      if (!valida(tab, o, cs)) { vencedor = outro; if (motivo === 'normal') motivo = 'ilegal:' + quem; break; }
      if (dt > tq + folga) { vencedor = outro; motivo = 'tempo:' + quem + ':' + dt.toFixed(0); break; }
      aplicar(tab, cs, o); jogadas.push(cs); o = outro;
    }
    const ganhaA = (vencedor === 'V') === aEhV;
    process.send({ id, aEhV, vencedor, ganhaA, motivo, n: jogadas.length, nab: ab.length, tmax, jogadas });
  });
}

// ---------- principal ----------
function principal() {
  const args = process.argv.slice(2);
  const get = (k, d) => { const i = args.indexOf(k); return i >= 0 && i + 1 < args.length ? args[i + 1] : d; };
  const fa = args[0], fb = args[1];
  if (!fa || !fb || fa.startsWith('--')) { console.log('Uso: node arena.js A.js B.js [--jogos N] [--tempo ms] [--proc n] [--abertura k] [--seed s] [--out f.jsonl]'); return; }
  const jogos = +get('--jogos', 100), tempo = +get('--tempo', 500), nproc = +get('--proc', 4);
  const tA = +get('--tempoA', 0), tB = +get('--tempoB', 0);
  const kab = +get('--abertura', 0), seed = +get('--seed', 1), out = get('--out', null), folga = +get('--folga', 0);
  const rng = mulberry32(seed);
  const jobs = [];
  const abFix = get('--aberturas', null) ? JSON.parse(fs.readFileSync(get('--aberturas', null), 'utf8')) : null;
  for (let g = 0; g < jogos; g += 2) {
    const ab = abFix ? abFix[(g / 2) % abFix.length] : abertura(rng, kab), s1 = Math.floor(rng() * 2 ** 31), s2 = Math.floor(rng() * 2 ** 31);
    const soA = get('--soA', null);
    jobs.push({ id: g, ab, aEhV: soA ? soA === 'V' : true, seed: s1 });
    if (g + 1 < jogos) jobs.push({ id: g + 1, ab, aEhV: soA ? soA === 'V' : false, seed: s2 });
  }
  const res = []; let prox = 0, ativos = 0;
  const t0 = Date.now();
  const fout = out ? fs.openSync(out, 'w') : null;
  const resumo = () => {
    const w = res.filter(r => r.ganhaA).length, n = res.length;
    const wV = res.filter(r => r.aEhV && r.ganhaA).length, nV = res.filter(r => r.aEhV).length;
    const wH = res.filter(r => !r.aEhV && r.ganhaA).length, nH = res.filter(r => !r.aEhV).length;
    const p = n ? w / n : 0, se = n ? Math.sqrt(p * (1 - p) / n) : 0;
    const vV = res.filter(r => r.vencedor === 'V').length;
    return `${path.basename(fa)} vs ${path.basename(fb)}: ${w}/${n} = ${(100 * p).toFixed(1)}% ±${(196 * se).toFixed(1)}  ` +
      `(A de V ${wV}/${nV}, A de H ${wH}/${nH}; V ganhou ${vV}/${n})  ${((Date.now() - t0) / 1000).toFixed(0)}s`;
  };
  for (let i = 0; i < Math.min(nproc, jobs.length); i++) {
    const w = fork(__filename, [], { env: Object.assign({}, process.env, { ARENA_WORKER: '1', ARENA_CFG: JSON.stringify([fa, fb, tempo, folga, tA, tB]) }) });
    ativos++;
    const enviar = () => { if (prox < jobs.length) w.send(jobs[prox++]); else w.send('fim'); };
    w.on('message', r => {
      res.push(r);
      if (fout) fs.writeSync(fout, JSON.stringify(r) + '\n');
      if (r.motivo !== 'normal') console.log('  partida', r.id, r.motivo);
      if (res.length % 10 === 0) console.log(resumo());
      enviar();
    });
    w.on('exit', () => { if (--ativos === 0) { console.log('FINAL ' + resumo()); const tm = { A: 0, B: 0 }; for (const r of res) { tm.A = Math.max(tm.A, r.tmax.A); tm.B = Math.max(tm.B, r.tmax.B); } console.log(`tempo máx por jogada: A ${tm.A.toFixed(0)} ms, B ${tm.B.toFixed(0)} ms; média de jogadas ${(res.reduce((s, r) => s + r.n, 0) / res.length).toFixed(1)}`); } });
    enviar();
  }
}

if (process.env.ARENA_WORKER) worker(); else principal();
