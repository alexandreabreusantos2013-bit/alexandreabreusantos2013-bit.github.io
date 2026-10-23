'use strict';
// Gera o bloco de pesos (normalização incorporada) para colar no bot.
//   node embed.js pesos.json > bloco.js
const fs = require('fs');
const js = JSON.parse(fs.readFileSync(process.argv[2], 'utf8'));
const M = require('./evalml.js');
const NG = 64, NPAT = M.NPAT;
const HID = js.HID, nIn = js.nIn, mu = js.mu, sd = js.sd;
const r = x => +x.toPrecision(5);
let WG, WP, B1 = [], W2 = [], B2;
if (HID === 0) {
  const w = js.P[0]; B2 = js.P[1][0]; WG = new Array(NG).fill(0); WP = new Array(NPAT).fill(0);
  for (let j = 0; j < nIn; j++) { const wj = w[j] / sd[j]; B2 -= wj * mu[j]; if (j < NG) WG[j] = wj; else WP[j - NG] = wj * 0.1; }
} else {
  const w1 = js.P[0], b1 = js.P[1]; W2 = js.P[2].slice(); B2 = js.P[3][0];
  WG = new Array(HID * NG).fill(0); WP = new Array(HID * NPAT).fill(0);
  for (let h = 0; h < HID; h++) {
    let b = b1[h];
    for (let j = 0; j < nIn; j++) { const wj = w1[h * nIn + j] / sd[j]; b -= wj * mu[j]; if (j < NG) WG[h * NG + j] = wj; else WP[h * NPAT + j - NG] = wj * 0.1; }
    B1.push(b);
  }
}
const fmt = a => '[' + a.map(r).join(',') + ']';
console.log(`const MODELO_EMB = { HID: ${HID}, WG: ${fmt(WG)}, WP: ${fmt(WP)}, B1: ${fmt(B1)}, W2: ${fmt(W2)}, B2: ${r(B2)} };`);
