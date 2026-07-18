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
