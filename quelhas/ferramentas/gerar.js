'use strict';
// Gera partidas de auto-jogo (com aberturas aleatórias) e grava-as em JSONL.
//   node gen.js bot.js --jogos N --tempo ms --proc 4 --seed s --out f.jsonl [--kmax 4]
const path = require('path'), fs = require('fs');
const { fork } = require('child_process');
function mulberry32(a) { return function () { a |= 0; a = a + 0x6D2B79F5 | 0; let t = Math.imul(a ^ a >>> 15, 1 | a); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; }; }
const tabVazio = () => [...Array(10)].map(() => Array(10).fill(0));
function listar(tab, o) {
  const out = [];
  for (let a = 0; a < 10; a++) for (let s = 0; s < 10; s++) {
    const livre = i => (o === 'V' ? !tab[i][a] : !tab[a][i]);
    if (!livre(s)) continue;
    let e = s; while (e < 10 && livre(e)) e++;
    for (let l = 2; s + l <= e; l++) { const cs = []; for (let k = 0; k < l; k++) cs.push(o === 'V' ? [s + k, a] : [a, s + k]); out.push(cs); }
  }
  return out;
}
const aplicar = (tab, cs, o) => { for (const [r, c] of cs) tab[r][c] = o === 'V' ? 1 : 2; };
if (process.env.GEN_WORKER) {
  const [fb, tempo, kmax] = JSON.parse(process.env.GEN_CFG);
  const B = require(path.resolve(fb)), bot = B.escolherJogada;
  process.on('message', job => {
    if (job === 'fim') process.exit(0);
    const rng = mulberry32(job.seed);
    const tab = tabVazio(); let o = 'V'; const jog = [], est = [];
    const k = Math.floor(rng() * (kmax + 1));
    let venc = null;
    for (let i = 0; i < 200; i++) {
      const L = listar(tab, o);
      if (!L.length) { venc = o; break; }
      let cs;
      if (i < k) { cs = L[Math.floor(rng() * L.length)]; est.push('r'); }
      else { cs = bot(tab.map(r => r.slice()), o, { tempoMs: tempo, rng }); const u = B._ultimo; est.push(u ? (u.estado === 'ganha' ? 'W' : u.estado === 'perdida' ? 'L' : '?') : '?'); }
      aplicar(tab, cs, o); jog.push(cs); o = o === 'V' ? 'H' : 'V';
    }
    process.send({ id: job.id, k, venc, jogadas: jog, est });
  });
} else {
  const args = process.argv.slice(2);
  const get = (k, d) => { const i = args.indexOf(k); return i >= 0 && i + 1 < args.length ? args[i + 1] : d; };
  const fb = args[0], jogos = +get('--jogos', 100), tempo = +get('--tempo', 250), nproc = +get('--proc', 4);
  const seed = +get('--seed', 1), out = get('--out', 'jogos.jsonl'), kmax = +get('--kmax', 4);
  const rng = mulberry32(seed);
  const jobs = []; for (let g = 0; g < jogos; g++) jobs.push({ id: g, seed: Math.floor(rng() * 2 ** 31) });
  let prox = 0, feitos = 0; const t0 = Date.now();
  const fout = fs.openSync(out, 'a');
  for (let i = 0; i < nproc; i++) {
    const w = fork(__filename, [], { env: Object.assign({}, process.env, { GEN_WORKER: '1', GEN_CFG: JSON.stringify([fb, tempo, kmax]) }) });
    const enviar = () => { if (prox < jobs.length) w.send(jobs[prox++]); else w.send('fim'); };
    w.on('message', r => {
      fs.writeSync(fout, JSON.stringify(r) + '\n'); feitos++;
      if (feitos % 50 === 0) console.log(`${feitos}/${jogos}  ${((Date.now() - t0) / 1000).toFixed(0)}s`);
      enviar();
    });
    enviar();
  }
}
