const L = require('fs').readFileSync(process.argv[2], 'utf8').trim().split('\n').map(JSON.parse);
const by = {}; for (const g of L) { const k = Math.floor(g.id / 2); (by[k] = by[k] || []).push(g); }
let a2 = 0, a0 = 0, s = 0;
for (const k in by) { const p = by[k]; if (p.length < 2) continue; const w = p.filter(g => g.ganhaA).length; if (w === 2) a2++; else if (w === 0) a0++; else s++; }
console.log(`${process.argv[2]}: A ganha os 2: ${a2}, A perde os 2: ${a0}, dividido: ${s}  -> diferença ${a2 - a0} em ${a2 + a0 + s} pares`);
