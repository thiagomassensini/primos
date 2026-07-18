# Checkpoint 0.13.0 — fatoracao finita de Dirichlet Cp

Este checkpoint liga a carta finita literal ao fator analitico esperado sem
tomar nenhum limite.

## Termo positivo

Para os indices positivos da carta, foi definido

```text
dirichletTerm(s,n) = n^(-s)
```

usando a potencia complexa principal. Como os fatores sao casts de naturais
nao negativos, a Mathlib fornece multiplicatividade sem ambiguidade de ramo.

## Fatoracao dos centros

O kernel verificou, para primo `p`, todo `M` e todo `s : Complex`,

```text
p * sum_{m=1}^M (p*m)^(-s)
  = p^(1-s) * sum_{m=1}^M m^(-s).
```

Logo a carta finita fica na forma

```text
finiteChart_p,M(s)
  = sum_{n=1}^{pM+halfRange(p)} n^(-s)
    - p^(1-s) * sum_{m=1}^M m^(-s).
```

Essa e a identidade finita que, depois de uma passagem ao limite justificada,
produz formalmente o fator `1-p^(1-s)`.

## Uso das fontes de pesquisa

Os documentos do projeto confirmaram a formula-alvo da carta bracketada e o
ganho esperado de duas potencias das segundas diferencas. Eles foram usados
como mapa de enunciados, nao como provas importadas no Lean.

## Fronteira honesta

Ainda nao foram formalizados:

- convergencia dos prefixos e passagem ao limite em `Re(s)>1`;
- convergencia bracketada no dominio maior `Re(s)>-1`;
- identidade infinita com Genuine/zeta;
- equivalencia de zeros, certificado Green concreto ou RH.

## Evidencia de compilacao

- repositorio privado: `thiagomassensini/primos`;
- branch: `agent/lean-kernel-audit`;
- pull request: `#1` (rascunho);
- commit matematico: `8d941e55af4b1e4e1c6b325b6b07bc90aaa04e8c`;
- workflow run: `29653694412`;
- job verde: `88104213909`;
- resultado: auditoria estatica e `lake build --wfail` concluidos com sucesso.

## Endpoints principais

- `Analytic.Cp.dirichletTerm`;
- `Analytic.Cp.positiveDirichletPrefix`;
- `Analytic.Cp.dirichletTerm_alignedCenter`;
- `Analytic.Cp.prime_mul_dirichletTerm_eq_cpow_one_sub`;
- `Analytic.Cp.p_mul_centerSum_dirichlet_eq_cpow_mul_prefix`;
- `Analytic.Cp.finiteChart_dirichlet_eq_prefix_sub_cpow_mul_prefix`.
