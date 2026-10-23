// aberturas equilibradas: prefixos de partidas com 84-92 casas vivas e previsão do modelo entre 0.3 e 0.7
const fs = require('fs');
const M = require('./evalml.js'); const F = require('./feats.js');
M.carregarModelo(JSON.parse(fs.readFileSync(process.argv[3], 'utf8')));
const G = fs.readFileSync(process.argv[2], 'utf8').trim().split('\n').map(JSON.parse);
const out = [], seen = new Set();
const liveOf = t => { let n = 0; for (let r = 0; r < 10; r++) for (let c = 0; c < 10; c++) if (!t[r][c] && ((r > 0 && !t[r-1][c]) || (r < 9 && !t[r+1][c]) || (c > 0 && !t[r][c-1]) || (c < 9 && !t[r][c+1]))) n++; return n; };
for (const g of G) {
  const tab = [...Array(10)].map(() => Array(10).fill(0)); let o = 'V';
  for (let i = 0; i < g.jogadas.length; i++) {
    const L = liveOf(tab);
    if (L >= +process.argv[4] && L <= +process.argv[5] && i >= 2) {
      const rows = tab.map(row => row.reduce((a, x, c) => a | (x ? 0 : 1 << c), 0));
      const R = o === 'V' ? rows : F.transpor(rows), C = F.transpor(R);
      const p = 1 / (1 + Math.exp(-M.avaliarML(R, C)));
      const k = rows.join(',') + o;
      if (p > 0.3 && p < 0.7 && !seen.has(k)) { seen.add(k); out.push(g.jogadas.slice(0, i)); }
      break;
    }
    for (const [r, c] of g.jogadas[i]) tab[r][c] = 1; o = o === 'V' ? 'H' : 'V';
  }
  if (out.length >= +process.argv[6]) break;
}
fs.writeFileSync(process.argv[7], JSON.stringify(out));
console.log('aberturas', out.length, 'plies médias', (out.reduce((a, x) => a + x.length, 0) / out.length).toFixed(1));
