# Checkpoint 0.15.0 — carta Cp bracketada

Este checkpoint liga, no kernel, a carta Genuine finita a serie de segundas
diferencas que converge no semiplano maior `Re(s)>-1`.

## Identidade finita da braquetada

Para primo impar, os offsets balanceados nao nulos sao reindexados como os
pares `-j,+j`, com `1 <= j <= halfRange(p)`. O kernel verificou, em qualquer
anel comutativo,

```text
Genuine.Cp.bracket p f center
  = saturatedBracket (halfRange p) f center.
```

Essa igualdade nao usa limites, potencias complexas ou zeta.

## Ganho de duas potencias

Uma desigualdade abstrata de segunda diferenca foi provada aplicando duas
vezes a desigualdade de valor medio. Se `||f''|| <= C` no intervalo relevante,
entao

```text
||f(c-r) - 2f(c) + f(c+r)|| <= 2*C*r^2.
```

Para `f_s(x)=x^(-s)`, o kernel verificou as derivadas e a identidade de norma

```text
||f_s''(x)|| = ||s(s+1)|| * x^(-Re(s)-2).
```

Somando os raios finitos da camera, cada bloco e dominado por uma constante
explicita vezes `(k+1)^(-Re(s)-2)`. A p-serie resultante e somavel quando
`Re(s)>-1`.

## Passagem ao limite Genuine

Cada prefixo da nova serie foi identificado literalmente com a carta ja
formalizada:

```text
finiteBracketedDirichletChart p M s
  = Genuine.Cp.finiteChart p M (dirichletTerm s).
```

Logo, para primo impar e `Re(s)>-1`, os prefixos Genuine convergem para
`bracketedDirichletChart p s`.

No semiplano comum `Re(s)>1`, o checkpoint anterior ja fazia a mesma
sequencia finita convergir para `(1-p^(1-s))*genuineDirichlet(s)`. Pela
unicidade do limite, o kernel elaborou

```text
bracketedDirichletChart p s
  = (1-p^(1-s))*genuineDirichlet(s).
```

## Fronteira honesta

Foi provada somabilidade absoluta para cada `s` com `Re(s)>-1`. Ainda nao foi
provado um majorante uniforme sobre compactos, nem a holomorfia do `tsum`.
Portanto este checkpoint nao chama a igualdade no dominio maior de
continuacao analitica e nao deriva equivalencia de zeros, certificado Green,
operador Hilbert--Polya ou RH.

## Evidencia de compilacao

- repositorio privado: `thiagomassensini/primos`;
- branch: `agent/lean-kernel-audit`;
- pull request: `#1` (rascunho);
- commit matematico: `af30c410ed6c68f4f4d9a35a4d88435a592b55c8`;
- workflow run: `29662384450`;
- job verde: `88127131010`;
- resultado: auditoria estatica e `lake build --wfail` concluidos com sucesso.

## Endpoints principais

- `Analytic.norm_centeredSecondDifference_le`;
- `Analytic.norm_realDirichletPower_centeredSecondDifference_le`;
- `Genuine.Cp.bracket_eq_saturatedBracket`;
- `Analytic.Cp.summable_norm_realCpSaturatedBracket`;
- `Analytic.Cp.finiteBracketedDirichletChart_eq_finiteChart`;
- `Analytic.Cp.finiteChart_dirichlet_tendsto_bracketedDirichletChart`;
- `Analytic.Cp.bracketedDirichletChart_eq_genuine_factor`.
