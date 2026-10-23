# Ferramentas do bot de Quelhas

O bot é só `../bot_novo.js`. Estes scripts servem para regenerar a avaliação e o livro e para medir versões.
Os pesos e o livro embutidos na versão atual estão em `pesos_g123_h8.json` e `livro_c4.json`
(`node build.js ../bot_novo.js pesos_g123_h8.json livro_c4.json` reconstrói exatamente o mesmo ficheiro).
Correm em Node puro, sem dependências, a partir desta pasta.

## Ciclo de treino da avaliação

```sh
# 1. auto-jogo com aberturas aleatórias (0 a 4 jogadas ao acaso); grava também o veredicto do solver em cada jogada
node gerar.js ../bot_novo.js --jogos 3000 --tempo 250 --proc 4 --seed 1 --out jogos.jsonl

# 2. rótulos: exatos a partir do 1.º ponto provado (e resolvendo para trás, --lim ms por posição);
#    antes disso, o valor do 1.º ponto provado
node rotular.js jogos.jsonl --out dados.jsonl --lim 1500 --proc 4

# 3. rede 148-8-1 (--hid 8, a usada no bot) ou regressão logística (--hid 0), posições com 50 a 100 casas vivas
node train.js dados.jsonl [mais_dados.jsonl ...] --hid 8 --ep 12 --lr 0.002 --min 50 --max 100 --out pesos.json

# 4. embutir os pesos (e opcionalmente o livro) no bot
node build.js ../bot_novo.js pesos.json [livro.json]
```

`feats.js` (extração de características usada no treino) e `evalml.js` (a mesma avaliação, rápida) têm de
ficar iguais à função `globais`/`avaliarML` do bot.

## Livro de aberturas

```sh
node mklivro.js ../bot_novo.js --col 4 --tempo 12000 --proc 4 --out livro.json
node build.js ../bot_novo.js pesos.json livro.json
```

Abre com a coluna 4 inteira e calcula, para cada resposta de H (módulo simetrias), a 2.ª jogada de V com 12 s.

## Medir

```sh
# partidas entre dois bots (aos pares, cores trocadas)
node ../arena.js A.js B.js --jogos 100 --tempo 500 --proc 4
# aberturas equilibradas (prefixos de partidas reais com 82-94 casas vivas e previsão entre 30 e 70%)
node mkab.js jogos.jsonl pesos.json 82 94 500 aberturas.json
node ../arena.js A.js B.js --jogos 1000 --aberturas aberturas.json --out r.jsonl && node pares.js r.jsonl
# conversão de posições ganhas (o bot mantém a vitória?)
node suite.js criar dados.jsonl --n 200 --min 72 --max 84 --out suite.json
node suite.js jogar A.js suite.json --out jog_A.json && node suite.js avaliar jog_A.json
```

`pares.js` conta os pares decisivos (o mesmo bot ganha com as duas cores), que é onde se vê a diferença
entre versões próximas: a maior parte dos pares fica dividida porque a abertura já decide.
