# Checkpoint 0.7.0 — reindexacao ponderada finita Cp

Este checkpoint transforma a bijecao global e a profundidade efetiva Cp numa
identidade de somas finitas com bordo totalmente explicito.

## Termos dos dois canais

Para uma perna `n` nao multipla de um primo impar `p`, o canal direto usa

```text
nonmultipleTerm(n)
  = depthWeight(effectiveDepth(p,n)) * value(n).
```

Para uma incidencia `x=(c,a)`, o canal centro--offset usa

```text
incidenceTerm(x)
  = depthWeight(padicValInt(p,c)) * value(c+a).
```

O kernel verificou que esses termos coincidem quando `x` e a incidencia
canonica de `n`. A prova usa simultaneamente:

- a recuperacao literal `c+a=n` da bijecao global;
- `effectiveDepth(p,n)=padicValInt(p,c)` do checkpoint 0.6.0.

## Reindexacao exata

Para qualquer caixa finita `L` de pernas,

```text
sum(n in L, nonmultipleTerm(n))
  = sum(x in incidenceImage(L), incidenceTerm(x)).
```

Nao existe fator de normalizacao, aproximacao ou perda de multiplicidade: a
igualdade e a reindexacao de um `Finset` por uma equivalencia.

## Bordo explicito

Dada uma caixa esperada `E` de incidencias, definimos

```text
extras    = incidenceImage(L) \ E
faltantes = E \ incidenceImage(L).
```

O teorema principal e

```text
direct(L)
  = expected(E) + sum(extras) - sum(faltantes).
```

Se `incidenceImage(L)=E`, o kernel deriva imediatamente a igualdade sem bordo.

## Endpoints Lean

- `Carry.Cp.incidenceImage`;
- `Carry.Cp.nonmultipleTerm`;
- `Carry.Cp.incidenceTerm`;
- `Carry.Cp.incidenceTerm_incidenceOfNonmultiple`;
- `Carry.Cp.incidenceTerm_nonmultipleEquivIncidence`;
- `Carry.Cp.weighted_reindex`;
- `Carry.Cp.extraIncidences`;
- `Carry.Cp.missingIncidences`;
- `Carry.Cp.finset_sum_eq_expected_add_boundary`;
- `Carry.Cp.weighted_reindex_with_boundary`;
- `Carry.Cp.weighted_reindex_of_exact_cover`.

Arquivo principal: `CPFormal/Carry/CpWeightedReindex.lean`.

## Evidencia de compilacao

- repositorio privado: `thiagomassensini/primos`;
- branch: `agent/lean-kernel-audit`;
- pull request: `#1` (rascunho);
- commit matematico: `52afc4ffa81f0d62ed732b86de3c4c7f3537284a`;
- workflow run: `29640821068`;
- job: `88070933888`;
- resultado: auditoria estatica e `lake build --wfail` concluidos com sucesso.

## Alcance exato

Este checkpoint e finito e algebrico. Ele ainda nao escolhe uma familia
concreta de caixas Cp, nao passa ao infinito e nao afirma convergencia,
identidade com zeta ou funcoes L, equivalencia de zeros, operador
Hilbert--Polya autoadjunto ou RH.

O proximo passo e construir caixas alinhadas Cp cuja caixa de pernas seja
exatamente a pre-imagem da caixa de incidencias. Nelas, `extras` e `faltantes`
serao ambos o `Finset` vazio por teorema.
