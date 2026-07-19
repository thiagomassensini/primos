# Registro da primeira auditoria no kernel

Este arquivo abre o primeiro ciclo de integracao continua do CPFormal.

O pull request correspondente deve permanecer em rascunho enquanto houver
erros de elaboracao. Cada correcao sera registrada em commit separado. Um
workflow verde autoriza promover no ledger somente os lemas realmente
compilados; nao fecha pontes matematicas ainda marcadas como abertas.

## Primeiro resultado verde

- commit: `2a29c850389c888c6f1b5bde2dcb899fd261b559`;
- run: `29634840124`;
- comando decisivo: `lake build --wfail`;
- conclusao: `success`.

O nucleo Genuine-first foi promovido no ledger. A reserva espectral permanece
fora do escopo certificado.

## Checkpoint de reindexacao ponderada C2

- commit: `0cc016b69419b811cbf12867f46605280ecdf7db`;
- run: `29635654651`;
- job: `88057413962`;
- comando decisivo: `lake build --wfail`;
- conclusao: `success`.

Foram elaborados pelo kernel `weighted_reindex`, a identidade generica de
bordo, `weighted_reindex_with_boundary` e o corolario de cobertura exata.

## Checkpoint de caixa alinhada C2

- commit: `45b7fe8bb761117609054f0b448c8c11db375b78`;
- run: `29636078858`;
- job: `88058546887`;
- comando decisivo: `lake build --wfail`;
- conclusao: `success`.

Foram elaborados pelo kernel a caixa concreta de incidencias nos centros
`4,8,...,4M`, sua caixa de pernas, a cobertura exata, o esvaziamento dos dois
termos de bordo e a igualdade ponderada resultante.

## Checkpoint de intervalo impar C2

- commit: `b6cdb634a1bbb25eb56709e964d9738e4d001e26`;
- run: `29636657680`;
- job: `88060082966`;
- comando decisivo: `lake build --wfail`;
- conclusao: `success`.

Foram elaboradas a alternancia esquerda/direita pelos indices pares e impares,
a igualdade da caixa com `3,5,...,4M+1`, a caracterizacao de pertinencia e a
cardinalidade exata `2M`.

## Checkpoint de residuos balanceados Cp

- commit: `211e2a09fa5312c5fb851de9f4a71f05209b0b24`;
- run: `29637023211`;
- job: `88061047891`;
- comando decisivo: `lake build --wfail`;
- conclusao: `success`.

Foram elaboradas a ida offset--residuo, a volta por `ZMod.valMinAbs`, as duas
leis de inversa e a cardinalidade `p-1` da camera balanceada.

## Checkpoint da bijecao global Cp

- commit: `e8b9cf7cedf15e7917d7837bb50bb6412d048ccb`;
- run: `29638936254`;
- job: `88066026811`;
- comando decisivo: `lake build --wfail`;
- conclusao: `success`.

O kernel elaborou a classe de inteiros nao multiplos de `p`, as incidencias
centro--offset, a escolha canonica do offset por residuo balanceado, a prova de
que o centro e divisivel por `p`, as duas leis de inversa e o teorema `∃!` da
decomposicao `n = centro + offset`.

## Checkpoint da profundidade efetiva Cp

- commit: `b24ea3d440198b779d30333df608a4cb0b2c78a0`;
- run: `29640037006`;
- job: `88068948411`;
- comando decisivo: `lake build --wfail`;
- conclusao: `success`.

Foram elaborados pelo kernel a unicidade do offset que produz divisibilidade
por `p`, a profundidade zero de cada offset nao canonico, a igualdade entre o
supremo das profundidades da carta e a profundidade do centro canonico, e a
positividade dessa profundidade quando o centro nao e zero.

## Checkpoint da reindexacao ponderada Cp

- commit: `52afc4ffa81f0d62ed732b86de3c4c7f3537284a`;
- run: `29640821068`;
- job: `88070933888`;
- comando decisivo: `lake build --wfail`;
- conclusao: `success`.

Foram elaborados pelo kernel a preservacao termo a termo do valor e do peso de
profundidade pela equivalencia Cp, a reindexacao de qualquer `Finset` de
pernas, a identidade de bordo `extras - faltantes` e o corolario de cobertura
exata.

## Checkpoint de caixa alinhada Cp

- commit: `49f8d226f1f9718fb15d76b89c5934f9852e8303`;
- run: `29642943076`;
- job: `88076344500`;
- comando decisivo: `lake build --wfail`;
- conclusao: `success`.

Foram elaborados pelo kernel a familia concreta de incidencias nos centros
`p,2p,...,Mp`, a ausencia de colisoes, as cardinalidades `M(p-1)`, a caixa
direta obtida pela bijecao Cp, a cobertura exata, o esvaziamento dos dois
termos de bordo e a igualdade ponderada resultante.

## Checkpoint dos pesos, norma de ramo e tilt Cp

- commit: `aec9140c36ed5274a8eb7e8a919ef86c0971c5e9`;
- run: `29644692098`;
- job verde: `88080985687`;
- comando decisivo: `lake build --wfail`;
- conclusao: `success`.

Foram elaborados pelo kernel os pesos `p^(-k)` e `p^(-k/2)`, a identidade
quadratica local, sua reindexacao pela geometria de carry, a serie infinita da
norma do ramo Cp, sua forma fechada, o criterio unitario na meia abscissa, o
tilt multirramo e a seta de saturacao da norma para anulacao do tilt.

## Checkpoint da rigidez do tilt Cp

- commit: `4ed11cfed623a94982a7ba3316f5a290c16fb4c9`;
- run: `29647362054`;
- job: `88087733439`;
- comando decisivo: `lake build --wfail`;
- conclusao: `success`.

Foram elaborados pelo kernel o pareamento exato das pernas `±a`, a escrita do
tilt como soma de segundas diferencas centradas, os dois regimes de sinal e a
construcao canonica de `TiltRigidityAt` para centros fora da camera.

## Checkpoint da carta finita e do criterio Green

- commit: `e9b8c3d9cd3e13b7085db35b9947743204fcf5b1`;
- run: `29648404437`;
- job: `88090470740`;
- comando decisivo: `lake build --wfail`;
- conclusao: `success`.

O kernel elaborou a abertura do bracket como bloco completo menos `p` copias
do centro, a identidade da carta finita em todos os primeiros `M` centros e o
teorema que converte um `SignedGreenCertificate` concreto em deslocamento
critico nulo, tilt nulo e `GenuineBranchBridge`. O run nao construiu o
certificado concreto nem provou a RH.

## Checkpoint do ladrilhamento literal da carta Cp

- commit: `bad4f56825e0d42d0fc628c3a54a46d8503865bf`;
- run: `29649780593`;
- job: `88094014871`;
- comando decisivo: `lake build --wfail`;
- conclusao: `success`.

O kernel verificou que cada bloco completo e o intervalo inteiro transladado,
que os blocos nos centros `p,2p,...,Mp` sao adjacentes e ladrilham exatamente
`1,...,pM+halfRange(p)`, e que a carta finita e esse prefixo literal menos
`p` vezes a soma dos centros. Uma tentativa anterior falhou apenas porque a
tatica automatica nao cancelou `center` numa igualdade; a prova corrigida usa
cancelamento aditivo exato. Nao foram introduzidas potencias complexas,
limites, zeros ou um certificado Green concreto.

## Checkpoint da fatoracao finita de Dirichlet Cp

- commit: `8d941e55af4b1e4e1c6b325b6b07bc90aaa04e8c`;
- run: `29653694412`;
- job: `88104213909`;
- comando decisivo: `lake build --wfail`;
- conclusao: `success`.

O kernel elaborou o monomio principal `n^(-s)` nos inteiros positivos, sua
multiplicatividade nos centros alinhados e a identidade

```text
p * sum_{m=1}^M (p*m)^(-s)
  = p^(1-s) * sum_{m=1}^M m^(-s).
```

Combinada ao ladrilhamento anterior, ela fornece a carta finita de Dirichlet
como prefixo longo menos o prefixo curto fatorado. O run nao tomou limites,
nao usou zeta e nao certificou convergencia ou equivalencia de zeros.

## Checkpoint da passagem ao limite Cp em `Re(s)>1`

- commit: `44a539e2c432f88d1bda4670ff3daba1a287819e`;
- run: `29656769332`;
- job: `88112424965`;
- comando decisivo: `lake build --wfail`;
- conclusao: `success`.

O kernel elaborou a somabilidade da serie positiva, a convergencia de seus
prefixos, a divergencia do cutoff `pM+halfRange(p)` e a passagem ao limite

```text
finiteChart_p,M(s)
  -> (1-p^(1-s)) * genuineDirichlet(s)
```

para primo impar e `Re(s)>1`. `genuineDirichlet` foi definido pela propria
serie, sem identificar por definicao o objeto com `riemannZeta`.

Este run nao certifica convergencia bracketada em `Re(s)>-1`, continuacao
analitica, equivalencia de zeros, certificado Green concreto ou RH.

## Checkpoint da passagem bracketada Cp

- commit: `af30c410ed6c68f4f4d9a35a4d88435a592b55c8`;
- run: `29662384450`;
- job: `88127131010`;
- comando decisivo: `lake build --wfail`;
- conclusao: `success`.

O kernel elaborou a identidade finita entre o bracket Genuine e o bracket
saturado, o ganho de duas potencias, a somabilidade absoluta para
`Re(s)>-1`, a passagem dos prefixos Genuine ao limite bracketado e a
identificacao com `(1-p^(1-s))*genuineDirichlet(s)` em `Re(s)>1` pela
unicidade do limite.

O run nao promoveu a afirmacao de continuacao analitica: ainda faltam
convergencia localmente uniforme em compactos e holomorfia da soma.

## Checkpoint da holomorfia e continuacao unica Cp

- commit: `da0585ced6f3922da6b32d57b54f169910357ca7`;
- run: `29665212572`;
- job: `88134403089`;
- comando decisivo: `lake build --wfail`;
- conclusao: `success`.

O kernel elaborou a diferenciabilidade de cada bloco na variavel espectral,
um majorante uniforme somavel numa bola canonica em torno de cada ponto de
`Re(s)>-1`, a holomorfia do `tsum` e da carta completa e a preconexidade do
semiplano. Pelo principio da identidade, a carta e a unica continuacao
analitica da identidade com o fator Genuine conhecida em `Re(s)>1`.

O run nao certifica identificacao com `riemannZeta`, nao anulacao do fator,
equivalencia de zeros, certificado Green concreto ou RH.

## Checkpoint do fator Cp e quociente Genuine

- commit: `26379be9ed40c9196bd85af8bcba6b2808cf2481`;
- run: `29667470934`;
- job: `88140361964`;
- comando decisivo: `lake build --wfail`;
- conclusao: `success`.

O kernel elaborou o confinamento dos zeros de `1-p^(1-s)` a `Re(s)=1`, a
nao anulacao no interior da faixa critica, a analiticidade do fator e do
quociente Cp, a recuperacao da serie Genuine em `Re(s)>1` e a equivalencia
entre zeros da carta e do quociente dentro da faixa.

O run nao certifica compatibilidade entre quocientes de primos diferentes,
identificacao com `riemannZeta`, preservacao de multiplicidade, certificado
Green concreto ou RH.

## Checkpoint da compatibilidade Genuine entre cameras Cp

- commit: `a31645bbf79a2743ab14bfbd0343c30b8b6f510c`;
- run: `29668593622`;
- job: `88143422851`;
- comando decisivo: `lake build --wfail`;
- conclusao: `success`.

O kernel elaborou a identidade cruzada entre duas cartas primas no semiplano
`Re(s)>1`, sua extensao a `Re(s)>-1` pelo principio da identidade e o
cancelamento dos dois fatores somente dentro da faixa critica, onde sua nao
anulacao ja estava provada. Como consequencia, os quocientes de quaisquer
primos impares coincidem na faixa e definem um unico representante
`genuineContinuation`; os zeros de toda carta prima impar sao exatamente os
zeros desse representante.

O run nao identifica `genuineContinuation` com `riemannZeta`, nao trata
multiplicidades, nao constroi o certificado Green concreto, nao constroi um
operador Hilbert--Polya e nao prova RH.

## Checkpoint Green Cp finito e endpoint refletido

- commit: `7b1275cf6af93a3c03be53e80f780127b42c7b6c`;
- run: `29670152564`;
- job: `88147549171`;
- comando decisivo: `lake build --wfail`;
- conclusao: `success`.

O kernel elaborou a identidade Green finita, o autovetor exato do bloco Cp,
a fatoracao finita do fluxo refletido e o decaimento exato do endpoint externo
`(M+1)^(-1) -> 0`. O run nao certifica ainda a positividade da energia
refletida, a identificacao do endpoint interno com a porta Genuine, uma
instancia concreta de `SignedGreenCertificate`, operador Hilbert--Polya ou RH.
