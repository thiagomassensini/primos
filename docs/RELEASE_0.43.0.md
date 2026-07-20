# Checkpoint 0.43 — somacao por partes da sintese escalar

## Coracao

O checkpoint 0.42 isolou o setor perdido pela compressao escalar como o
kernel centrado

```text
K_M(f)_m = M * f_m - S_M(f),
S_M(f)   = sum_{j<M} f_j.
```

Sua primitiva causal e

```text
P_M(f,k) = sum_{m<k} K_M(f)_m.
```

O 0.43 aplica somacao por partes a essa primitiva preservando cada registro.
Os dois endpoints ja provados no 0.42 entram literalmente:

```text
P_M(f,0) = 0,
P_M(f,M) = 0.
```

Portanto nenhum termo de bordo e descartado por limite ou por definicao.

## Formula fechada da primitiva

O kernel prova tambem, sem recursao,

```text
P_M(f,k) = M * S_k(f) - k * S_M(f).
```

Na porta angular Genuine isso vira

```text
P_M(Phi,k)
  = M * finiteCanonicalAngularTrace(k,s)
      - k * finiteCanonicalAngularTrace(M,s).
```

Assim a primitiva usada por Abel e formada pelos mesmos tracos angulares que
o 0.41 abriu como somas de segundas diferencas. Nao foi introduzido um novo
operador.

## Identidade de Abel sem bordo

Para duas familias `f` e `g`, a somacao por partes produz

```text
KernelPairing_M(f,g)
  = sum_{m<M-1}
      conj(P_M(f,m+1))
        * (K_M(g)_m - K_M(g)_(m+1)).
```

A constante de centralizacao desaparece sob a diferenca:

```text
K_M(g)_m - K_M(g)_(m+1)
  = M * (g_m - g_(m+1)).
```

Definindo

```text
ClosedBulk_M(f,g)
  = sum_{m<M-1}
      conj(P_M(f,m+1)) * (g_m-g_(m+1)),
```

segue a identidade exata

```text
KernelPairing_M(f,g) = M * ClosedBulk_M(f,g).
```

Nao sobra cutoff externo nem endpoint interno.

## Ledger angular desescalado

Especializando nos blocos angulares em `s` e `s#`, escreva

```text
B_M = finiteCanonicalAngularClosedSynthesisBulk(M,s),
G_M = finiteReflectedGradientPairing(3M,s),
L_M = finiteCanonicalAngularLocalGreenCorrection(M,s),
C_M = finiteCanonicalAngularGreenCorrection(M,s).
```

Para `M>0`, o ledger do 0.42 perde seu fator comum e fica

```text
C_M + B_M = (M-1) * G_M + M * L_M.
```

Toda a comparacao entre o bulk de Abel e a correcao local pode entao ser
concentrada num unico objeto tipado:

```text
D_M = M * L_M - B_M.
```

O kernel prova

```text
C_M = (M-1) * G_M + D_M,

ScalarAngularPairing_M = M * G_M + D_M.
```

A segunda igualdade inclui `M=0`. Ela substitui a antiga interferencia
off-diagonal por um bulk fechado com proveniencia e uma comparacao local
explicita.

## Genuine-first

Num unico zero de `genuineContinuation` no strip, o observavel escalar ja
convergia a zero. Pela igualdade anterior, o kernel transporta esse fato sem
nova hipotese para

```text
M * G_M + D_M -> 0.
```

E, depois do coeficiente radial herdado do carry,

```text
cpRadialDifference(p,delta) * (M * G_M + D_M) -> 0.
```

O tilt nao e reprovado e o Green nao e redefinido. A nova escrita apenas
localiza exatamente onde um cancelamento capaz de esconder a energia Green
teria de viver.

## Obstrucao finita honesta

O cancelamento `D_M=0` nao vale por identidade universal. No primeiro bloco,
o bulk interbloco e vazio e

```text
D_1(s) = canonicalAngularLocalGreenCorrection(0,s).
```

No witness aritmetico `s=2`, o kernel calcula

```text
D_1(2) = -103/48 != 0.
```

Esse ponto esta fora do strip. O witness serve somente para impedir que a
comparacao local--bulk seja apagada universalmente; ele nao decide o limite
sob a hipotese de zero Genuine.

## Fronteira rigorosa

O checkpoint nao prova que `D_M` tende a zero nem que ele e pequeno em
relacao a `M * G_M`. O proximo gate e agora preciso: analisar o defeito
fechado `D_M` no regime Genuine e mostrar que ele nao pode cancelar a energia
radial positiva quando o coeficiente de tilt e nao nulo.

## Teoremas principais

- `finitePortSynthesisKernelPrefix_eq_scaled_prefix_sub_cutoff`;
- `finitePortSynthesisKernelPairing_summation_by_parts`;
- `finitePortSynthesisKernelPairing_eq_mul_closedBulk`;
- `finiteCanonicalAngularKernelPrefix_eq_centered_traces`;
- `finiteCanonicalAngularClosedSynthesisBulk_eq_centeredTraceBulk`;
- `finiteCanonicalAngularGreenCorrection_add_closedBulk`;
- `finiteCanonicalAngularGreenCorrection_eq_diagonalGrowth_add_closedBulkDefect`;
- `finiteCanonicalAngularScalarPairing_eq_mul_green_add_closedBulkDefect`;
- `finiteCanonicalAngularMulGreenAddClosedBulkDefect_tendsto_zero_of_genuine_zero`;
- `finiteCanonicalAngularRadialClosedBulkBudget_tendsto_zero_of_genuine_zero`;
- `finiteCanonicalAngularClosedBulkDefect_one_two_ne_zero`.

## Arquivos

- `CPFormal/Analytic/CpFiniteScalarSynthesisSummationByParts.lean`;
- `CPFormal.lean`;
- `docs/SOURCE_MAP.md`.

## Validacao local

```text
lake build --wfail
Build completed successfully (8713 jobs).
```

- auditoria estatica: **success**;
- elaboracao pelo kernel: **success**;
- axiomas reportados: somente `propext`, `Classical.choice` e `Quot.sound`;
- nenhum `sorry`, `admit` ou axioma local.

A evidencia remota sera registrada depois do workflow final do PR.
