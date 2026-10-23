'use strict';
// Livro: V abre com a jogada dada; para cada resposta de H (módulo simetrias) calcula a 2.ª jogada de V com tempo longo.
//   node mklivro.js bot.js --tempo 12000 --proc 4 --out livro.json [--col 4]
const fs = require('fs'), path = require('path');
const { fork } = require('child_process');
const args = process.argv.slice(2);
const get = (k, d) => { const i = args.indexOf(k); return i >= 0 && i + 1 < args.length ? args[i + 1] : d; };
const rev10 = m => { let r = 0; for (let b = 0; b < 10; b++) if ((m >> b) & 1) r |= 1 << (9 - b); return r; };
const rowsOf = tab => tab.map(row => row.reduce((a, x, c) => a | (x ? 0 : 1 << c), 0));
const chave = (rows, o) => rows.map(m => (m | 1024).toString(16)).join('') + o;
function canon(rows, o) { // menor chave entre as 4 simetrias
  let best = null;
  for (let sym = 0; sym < 4; sym++) {
    const r2 = []; for (let r = 0; r < 10; r++) { let m = rows[(sym & 1) ? 9 - r : r]; if (sym & 2) m = rev10(m); r2.push(m); }
    const k = chave(r2, o); if (best === null || k < best) best = k;
  }
  return best;
}
function encode(cs) {  // casas -> [dir, linha, início, comprimento]
  const v = cs.every(p => p[1] === cs[0][1]) && cs.length > 1 && cs[0][0] !== cs[1][0];
  if (v) return [0, cs[0][1], Math.min(...cs.map(p => p[0])), cs.length];
  return [1, cs[0][0], Math.min(...cs.map(p => p[1])), cs.length];
}
if (process.env.LIV_W) {
  const B = require(path.resolve(args[0]));
  process.on('message', m => {
    if (m === 'fim') process.exit(0);
    const t0 = Date.now();
    const cs = B.escolherJogada(m.tab, 'V', { tempoMs: +get('--tempo', 12000) });
    process.send({ i: m.i, cs, est: B._ultimo.estado, ms: Date.now() - t0 });
  });
} else {
  const col = +get('--col', 4);
  const tab0 = [...Array(10)].map(() => Array(10).fill(0));
  const first = []; for (let r = 0; r < 10; r++) first.push([r, col]);
  const t1 = tab0.map(r => r.slice()); for (const [r, c] of first) t1[r][c] = 1;
  // respostas de H
  const pos = [], seen = new Set();
  for (let r = 0; r < 10; r++) for (let s = 0; s < 10; s++) for (let l = 2; s + l <= 10; l++) {
    let ok = true; for (let c = s; c < s + l; c++) if (t1[r][c]) ok = false;
    if (!ok) continue;
    const t2 = t1.map(x => x.slice()); for (let c = s; c < s + l; c++) t2[r][c] = 2;
    const k = canon(rowsOf(t2), 'V'); if (seen.has(k)) continue; seen.add(k);
    pos.push(t2);
  }
  console.log('posições a analisar', pos.length);
  const livro = {}; livro[chave(rowsOf(tab0), 'V')] = encode(first);
  let prox = 0, feitos = 0; const est = {};
  for (let w = 0; w < +get('--proc', 4); w++) {
    const ch = fork(__filename, args, { env: Object.assign({}, process.env, { LIV_W: '1' }) });
    const enviar = () => { if (prox < pos.length) { const i = prox++; ch.send({ i, tab: pos[i] }); } else ch.send('fim'); };
    ch.on('message', r => {
      livro[chave(rowsOf(pos[r.i]), 'V')] = encode(r.cs);
      est[r.est] = (est[r.est] || 0) + 1;
      if (++feitos % 10 === 0 || feitos === pos.length) console.log(`${feitos}/${pos.length} ${JSON.stringify(est)}`);
      if (feitos === pos.length) fs.writeFileSync(get('--out', 'livro.json'), JSON.stringify(livro));
      enviar();
    });
    enviar();
  }
}
