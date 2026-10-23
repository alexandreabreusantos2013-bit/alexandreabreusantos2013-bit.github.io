'use strict';
// Suite de conversão: posições ganhas (exatas) — o bot escolhe uma jogada que mantém a vitória?
//   node suite.js criar dados.jsonl --n 200 --min 70 --max 84 --out suite.json
//   node suite.js jogar bot.js suite.json --out jog_bot.json [--tempo 500]   (corre em paralelo com --proc)
//   node suite.js avaliar jog_*.json  (resolve os filhos offline com cache)
const fs = require('fs'), path = require('path');
const { fork } = require('child_process');
const args = process.argv.slice(2);
const get = (k, d) => { const i = args.indexOf(k); return i >= 0 && i + 1 < args.length ? args[i + 1] : d; };
const rowsToTab = rows => rows.map(m => [...Array(10)].map((_, c) => (m >> c) & 1 ? 0 : 1));
function mulberry32(a) { return function () { a |= 0; a = a + 0x6D2B79F5 | 0; let t = Math.imul(a ^ a >>> 15, 1 | a); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; }; }
const modo = args[0];
if (modo === 'criar') {
  const rng = mulberry32(5);
  const L = fs.readFileSync(args[1], 'utf8').trim().split('\n').map(JSON.parse)
    .filter(d => d.tipo === 'x' && d.y === 1 && d.live >= +get('--min', 70) && d.live <= +get('--max', 84));
  const seen = new Set(), out = [];
  for (let i = L.length - 1; i > 0; i--) { const j = Math.floor(rng() * (i + 1)); [L[i], L[j]] = [L[j], L[i]]; }
  for (const d of L) { const k = d.rows.join(',') + d.o; if (seen.has(k)) continue; seen.add(k); out.push({ rows: d.rows, o: d.o, live: d.live }); if (out.length >= +get('--n', 200)) break; }
  fs.writeFileSync(get('--out', 'suite.json'), JSON.stringify(out));
  console.log('suite', out.length);
} else if (modo === 'jogar') {
  if (process.env.SU_W) {
    const B = require(path.resolve(args[1]));
    process.on('message', m => {
      if (m === 'fim') process.exit(0);
      const tab = rowsToTab(m.rows);
      const cs = B.escolherJogada(tab, m.o, { tempoMs: +get('--tempo', 500), rng: mulberry32(m.i + 1) });
      process.send({ i: m.i, cs });
    });
  } else {
    const S = JSON.parse(fs.readFileSync(args[2], 'utf8')), res = new Array(S.length);
    let prox = 0, feitos = 0;
    for (let w = 0; w < +get('--proc', 4); w++) {
      const ch = fork(__filename, args, { env: Object.assign({}, process.env, { SU_W: '1' }) });
      const enviar = () => { if (prox < S.length) { const i = prox++; ch.send({ i, rows: S[i].rows, o: S[i].o }); } else ch.send('fim'); };
      ch.on('message', r => { res[r.i] = r.cs; if (++feitos === S.length) fs.writeFileSync(get('--out', 'jog.json'), JSON.stringify({ suite: args[2], bot: args[1], jog: res })); enviar(); });
      enviar();
    }
  }
} else if (modo === 'avaliar') {
  const E = require('./solver_regioes.js');
  const cacheF = 'suite_cache.json';
  const cache = fs.existsSync(cacheF) ? JSON.parse(fs.readFileSync(cacheF, 'utf8')) : {};
  const files = args.slice(1).filter(a => !a.startsWith('--'));
  for (const f of files) {
    const J = JSON.parse(fs.readFileSync(f, 'utf8')), S = JSON.parse(fs.readFileSync(J.suite, 'utf8'));
    let ok = 0, mal = 0, desc = 0;
    const porL = {};
    for (let i = 0; i < S.length; i++) {
      const tab = rowsToTab(S[i].rows), o = S[i].o, cs = J.jog[i];
      for (const [r, c] of cs) tab[r][c] = 1;
      const key = tab.map(r => r.join('')).join('') + o;
      let v = cache[key];
      if (v === undefined) {
        try { v = E.resolver(tab, o === 'V' ? 'H' : 'V', +get('--lim', 20000)) ? 0 : 1; } catch (e) { v = -1; }
        cache[key] = v;
      }
      const b = Math.floor(S[i].live / 5) * 5; porL[b] = porL[b] || [0, 0]; porL[b][1]++;
      if (v === 1) { ok++; porL[b][0]++; } else if (v === 0) mal++; else desc++;
    }
    fs.writeFileSync(cacheF, JSON.stringify(cache));
    console.log(`${J.bot}: mantém vitória ${ok}/${S.length}, perde ${mal}, desconhecido ${desc}  | ` + Object.keys(porL).map(k => `${k}:${porL[k][0]}/${porL[k][1]}`).join(' '));
  }
}
