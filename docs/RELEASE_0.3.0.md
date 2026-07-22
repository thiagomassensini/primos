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
- a caixa concreta nos centros `4,8,...,4M`, com as duas pernas de cada
  centro, possui cobertura exata e bordo vazio.

Arquivos principais: `CPFormal/Carry/C2WeightedReindex.lean` e
`CPFormal/Carry/C2AlignedBox.lean`.

## Evidencia de compilacao

- repositorio privado: `thiagomassensini/primos`;
- branch: `agent/lean-kernel-audit`;
- pull request: `#1` (rascunho);
- commit: `45b7fe8bb761117609054f0b448c8c11db375b78`;
- GitHub Actions run: `29636078858`;
- resultado: `lake build --wfail` concluido com sucesso.

## O que este checkpoint nao afirma

Nao ha aqui passagem ao infinito, convergencia de series, identificacao com a
zeta, certificacao de zeros, operador de Hilbert--Polya ou prova da RH. O
proximo alvo e caracterizar diretamente a caixa de pernas como um intervalo
impar finito, provar sua cardinalidade e transportar a construcao para Cp.
