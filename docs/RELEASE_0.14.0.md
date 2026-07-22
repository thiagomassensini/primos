# Checkpoint 0.14.0 — passagem ao limite Cp em `Re(s)>1`

Este checkpoint fecha a primeira passagem infinita da carta Genuine Cp no
semiplano de convergencia absoluta.

## Genuine definido primeiro pela serie

O objeto inicial foi definido sem usar zeta como atalho:

```text
genuineDirichlet(s) = sum_{n>=1} n^(-s).
```

Para `Re(s)>1`, o kernel verificou a somabilidade dos termos e que os prefixos
`sum_{n=1}^N n^(-s)` convergem para esse `tsum`.

## Dois prefixos, um unico limite

A identidade finita do checkpoint anterior foi reescrita como

```text
finiteChart_p,M(s)
  = prefix(s, pM+halfRange(p))
    - p^(1-s) * prefix(s,M).
```

Para primo `p`, o cutoff longo `pM+halfRange(p)` tende a infinito. Portanto os
dois prefixos convergem para o mesmo `genuineDirichlet(s)`.

## Teorema principal

Para primo impar `p` e `Re(s)>1`, o kernel elaborou

```text
finiteChart_p,M(s)
  -> (1-p^(1-s)) * genuineDirichlet(s).
```

Endpoint Lean:

```text
Analytic.Cp.finiteChart_dirichlet_tendsto_genuine_factor
```

## O que isto fecha

- somabilidade da serie positiva no semiplano absoluto;
- convergencia dos prefixos curto e longo;
- passagem ao limite da carta finita Cp;
- aparecimento rigoroso do fator `1-p^(1-s)` a partir do cancelamento finito.

## Fronteira honesta

Este checkpoint ainda nao fornece:

- convergencia da serie bracketada no dominio maior `Re(s)>-1`;
- ganho formal de duas potencias da segunda diferenca;
- continuacao analitica;
- teorema identificando `genuineDirichlet` com a zeta de Riemann da Mathlib;
- nao anulacao do fator no critical strip ou equivalencia de zeros;
- certificado Green concreto, operador Hilbert--Polya ou RH.

Os documentos de pesquisa foram usados como mapa para a formula-alvo. A prova
Lean usa a identidade finita ja verificada e os teoremas de somabilidade e
limite da Mathlib.

## Evidencia de compilacao

- repositorio privado: `thiagomassensini/primos`;
- branch: `agent/lean-kernel-audit`;
- pull request: `#1` (rascunho);
- commit matematico: `44a539e2c432f88d1bda4670ff3daba1a287819e`;
- workflow run: `29656769332`;
- job verde: `88112424965`;
- resultado: auditoria estatica e `lake build --wfail` concluidos com sucesso.

## Endpoints principais

- `Analytic.Cp.genuineDirichlet`;
- `Analytic.Cp.summable_dirichletTerm_nat_add_one`;
- `Analytic.Cp.positiveDirichletPrefix_tendsto_genuineDirichlet`;
- `Analytic.Cp.positiveDirichletPrefix_eq_sum_Icc`;
- `Analytic.Cp.finiteChart_dirichlet_eq_two_prefixes`;
- `Analytic.Cp.chartCutoff_tendsto_atTop`;
- `Analytic.Cp.finiteChart_dirichlet_tendsto_genuine_factor`.
