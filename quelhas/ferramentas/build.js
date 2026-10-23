// injeta o modelo (e o livro) no bot: node build.js bot_novo.js pesos.json [livro.json]
const fs = require('fs'), { execFileSync } = require('child_process');
const [fbot, fw, flivro] = process.argv.slice(2);
let s = fs.readFileSync(fbot, 'utf8');
const bloco = execFileSync('node', [__dirname + '/embed.js', fw]).toString().trim();
s = s.replace(/\/\/ @@MODELO@@\n[\s\S]*?\/\/ @@FIM_MODELO@@\n/, '// @@MODELO@@\n' + bloco + '\n// @@FIM_MODELO@@\n');
if (flivro) {
  const L = JSON.parse(fs.readFileSync(flivro, 'utf8'));
  const linhas = Object.keys(L).sort().map(k => `  '${k}': [${L[k].join(', ')}],`).join('\n');
  s = s.replace(/\/\/ @@LIVRO@@\n[\s\S]*?\/\/ @@FIM_LIVRO@@\n/, '// @@LIVRO@@\nconst LIVRO = {\n' + linhas + '\n};\n// @@FIM_LIVRO@@\n');
}
fs.writeFileSync(fbot, s);
console.log('ok', fbot, s.length, 'bytes');
