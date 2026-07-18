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
