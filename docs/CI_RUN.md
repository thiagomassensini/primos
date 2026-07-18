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
