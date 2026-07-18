# Checkpoint 0.3.0 — reindexacao ponderada C2

Este checkpoint acrescenta ao nucleo Genuine-first a primeira ponte ponderada
completa entre pernas impares e incidencias de brackets C2.

## Resultados verificados pelo kernel

- a bijecao `OddLeg equiv Incidence` reindexa qualquer caixa finita;
- `effectiveDepth(n)` coincide com a profundidade 2-adica do centro adjacente;
- qualquer funcao de peso da profundidade e preservada pela bijecao;
- para caixas finitas arbitrarias,
  `direct = expected + extra - missing`;
- quando a cobertura e exata, o bordo desaparece literalmente.

Arquivo principal: `CPFormal/Carry/C2WeightedReindex.lean`.

## Evidencia de compilacao

- repositorio privado: `thiagomassensini/primos`;
- branch: `agent/lean-kernel-audit`;
- pull request: `#1` (rascunho);
- commit: `0cc016b69419b811cbf12867f46605280ecdf7db`;
- GitHub Actions run: `29635654651`;
- resultado: `lake build --wfail` concluido com sucesso.

## O que este checkpoint nao afirma

Nao ha aqui passagem ao infinito, convergencia de series, identificacao com a
zeta, certificacao de zeros, operador de Hilbert--Polya ou prova da RH. O
proximo alvo e definir caixas aritmeticas alinhadas e provar que seu bordo e
vazio (ou controlar o bordo quando nao for).
