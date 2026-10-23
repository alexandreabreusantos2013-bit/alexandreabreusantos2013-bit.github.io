'use strict';
// Rotulagem usando os veredictos do bot (est: W/L/?/r por jogada). Depois do 1.º ponto provado, tudo é exato.
// Antes disso tenta resolver para trás com --lim ms; o resto recebe o valor do 1.º ponto provado (tipo 'm').
//   node label2.js jogos.jsonl --out dados.jsonl --lim 1500 --proc 4
const path = require('path'), fs = require('fs');
const { fork } = require('child_process');
function liveCount(tab) {
  let live = 0;
  for (let r = 0; r < 10; r++) for (let c = 0; c < 10; c++) if (!tab[r][c] && ((r > 0 && !tab[r - 1][c]) || (r < 9 && !tab[r + 1][c]) || (c > 0 && !tab[r][c - 1]) || (c < 9 && !tab[r][c + 1]))) live++;
  return live;
}
if (process.env.LAB_WORKER) {
  const [eng, lim] = JSON.parse(process.env.LAB_CFG);
  const E = require(path.resolve(eng));
  process.on('message', g => {
    if (g === 'fim') process.exit(0);
    const tab = [...Array(10)].map(() => Array(10).fill(0)); let o = 'V'; const pos = [];
    for (const cs of g.jogadas) { pos.push([tab.map(r => r.slice()), o]); for (const [r, c] of cs) tab[r][c] = o === 'V' ? 1 : 2; o = o === 'V' ? 'H' : 'V'; }
    const n = pos.length, res = new Array(n).fill(null);
    let j = 0; while (j < n && g.est[j] !== 'W' && g.est[j] !== 'L') j++;
    let incons = 0;
    if (j < n) {
      const v = g.est[j] === 'W' ? 1 : 0;
      for (let i = j; i < n; i++) {
        res[i] = ((i - j) % 2 === 0) ? v : 1 - v;
        if ((g.est[i] === 'W' && res[i] !== 1) || (g.est[i] === 'L' && res[i] !== 0)) incons++;
      }
      // depois da última jogada quem tem a vez fica sem jogadas e ganha: quem fez a última jogada perdeu
      if (res[n - 1] !== 0) incons++;
      if (g.venc === pos[n - 1][1]) incons++;
    }
    let k = j - 1;
    for (; k >= 0; k--) {
      const [t, oo] = pos[k];
      try { res[k] = E.resolver(t, oo, lim) ? 1 : 0; } catch (e) { break; }
    }
    let j0 = 0; while (j0 < n && res[j0] === null) j0++;
    const out = [];
    for (let i = 0; i < n; i++) {
      const [t, oo] = pos[i];
      let y, tipo;
      if (res[i] !== null) { y = res[i]; tipo = 'x'; }
      else if (j0 < n) { y = ((j0 - i) % 2 === 0) ? res[j0] : 1 - res[j0]; tipo = 'm'; }
      else { y = (oo === g.venc) ? 1 : 0; tipo = 'r'; }
      out.push({ rows: t.map(row => row.reduce((a, x, c) => a | (x ? 0 : 1 << c), 0)), o: oo, live: liveCount(t), y, tipo, g: g.id, ply: i, k: g.k });
    }
    process.send({ out, incons });
  });
} else {
  const args = process.argv.slice(2);
  const get = (k, d) => { const i = args.indexOf(k); return i >= 0 && i + 1 < args.length ? args[i + 1] : d; };
  const inp = args[0], out = get('--out', 'dados.jsonl'), lim = +get('--lim', 1500), nproc = +get('--proc', 4), eng = get('--eng', 'solver_regioes.js');
  const jogos = fs.readFileSync(inp, 'utf8').trim().split('\n').map(JSON.parse);
  const fout = fs.openSync(out, 'w');
  let prox = 0, feitos = 0, incons = 0; const t0 = Date.now();
  for (let i = 0; i < nproc; i++) {
    const w = fork(__filename, [], { env: Object.assign({}, process.env, { LAB_WORKER: '1', LAB_CFG: JSON.stringify([eng, lim]) }) });
    const enviar = () => { if (prox < jogos.length) w.send(jogos[prox++]); else w.send('fim'); };
    w.on('message', r => {
      for (const x of r.out) fs.writeSync(fout, JSON.stringify(x) + '\n');
      incons += r.incons;
      if (++feitos % 200 === 0 || feitos === jogos.length) console.log(`${feitos}/${jogos.length} ${((Date.now() - t0) / 1000).toFixed(0)}s inconsistências ${incons}`);
      enviar();
    });
    enviar();
  }
}
