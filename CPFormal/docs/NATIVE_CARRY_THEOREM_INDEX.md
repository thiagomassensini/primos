# Índice canônico da teoria nativa do carry

## Regra de leitura

Este índice separa três propriedades que não podem ser fundidas por uma
definição:

1. equilíbrio quadrático da massa de carry;
2. anulação da câmera nativa/Genuine;
3. detecção Green do deslocamento transversal.

Os tipos Lean são a autoridade. Inventários de arquivos, versões e contagens
de declarações são auxiliares e não substituem a elaboração pelo kernel.

## Ordem canônica

| Camada | Fato central | Declarações | Fonte |
|---|---|---|---|
| Incidência posicional | quantidade preservada sob redistribuição por carry | `positionalUnitCarry_preserves_value`, `nonmultipleEquivIncidence` | `Carry/PositionalDecomposition.lean`, `Carry/CpGlobalIncidence.lean` |
| Massa | profundidade `k` possui massa `b^(-k)` | `criticalMass`, `uniformCarryEvent_probability` | `Carry/CpBranchWeight.lean`, `Carry/UniformCarryProbability.lean` |
| Amplitude | amplitude crítica é a raiz quadrática da massa | `criticalAmplitude`, `criticalAmplitude_sq_eq_mass` | `Carry/CpBranchWeight.lean` |
| Equilíbrio | compatibilidade amplitude--massa equivale a `sigma = 1/2` | `positionalCarryMassCompatible_iff`, `nativeCarryRealPlaneMassCompatible_iff` | `Analytic/CpPositionalCarryQuadraticRigidity.lean`, `Analytic/CpNativeCarryRealPlaneBracket.lean` |
| Câmera real | zero significa que a câmera tende a zero | `IsNativeCarryRealOperatorZero`, `isNativeCarryRealOperatorZero_iff` | `Analytic/CpNativeCarryRealOperatorZero.lean` |
| Embalagem complexa | a coordenada complexa preserva exatamente o zero real | `isNativeCarryComplexOperatorZero_iff_real` | `Analytic/CpNativeCarryComplexOperatorSameAsReal.lean` |
| Genuine | câmera real `3` e Genuine têm o mesmo zero no strip | `isNativeCarryRealOperatorZero_three_iff_genuineContinuation_zero` | `Analytic/CpNativeGenuineGreenCompletedCrosswalk.lean` |
| Green | o centro Green detecta `re(s)-1/2` | `complexifiedAlignedGreenLimitOperator_eq_zero_iff_criticalDisplacement_eq_zero` | `Analytic/CpGenuineGreenCompletedOperator.lean` |
| Operador completado | os dois canais zeram juntos exatamente em zero mais equilíbrio | `genuineGreenCompletedLimitOperator_eq_zero_iff_nativeZero_and_re_eq_half` | `Analytic/CpNativeGenuineGreenCompletedCrosswalk.lean` |

## Equilíbrio antes dos zeros

O carry posicional fornece a massa e sua realização quadrática:

```text
b^(-k) -> b^(-k/2) -> amplitude^2 = mass.
```

Ao deformar o expoente por `sigma`, o kernel prova:

```lean
NativeCarryRealPlaneMassCompatible sigma time
  ↔ sigma = (1 : ℝ) / 2
```

Esse é um teorema de compatibilidade energética. Ele não contém hipótese de
zero e não classifica o conjunto de zeros de uma função.

## Zero literal

O predicado canônico não inclui compatibilidade de massa:

```lean
def IsNativeCarryRealOperatorZero
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  NativeCarryRealOperatorBoundaryClosesAt camera sigma time
```

Assim, o teorema básico é propositalmente literal:

```lean
theorem isNativeCarryRealOperatorZero_iff
    (camera : ℕ) (sigma time : ℝ) :
    IsNativeCarryRealOperatorZero camera sigma time ↔
      NativeCarryRealOperatorBoundaryClosesAt camera sigma time
```

O nome `IsNativeCarryRealOperatorResonance camera time` é somente a
especialização desse predicado a `sigma = 1/2`; não é uma fatoração de todos
os zeros.

## Identidade nativo--Genuine

Dentro do strip, a equivalência é direta e vale em qualquer coordenada radial:

```lean
theorem isNativeCarryRealOperatorZero_three_iff_genuineContinuation_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    IsNativeCarryRealOperatorZero 3 s.re s.im ↔
      genuineContinuation s = 0
```

A embalagem complexa é apenas o mesmo par real escrito em `ℂ`:

```lean
IsNativeCarryComplexOperatorZero camera sigma time
  ↔ IsNativeCarryRealOperatorZero camera sigma time.
```

Nenhuma das duas equivalências deduz `sigma = 1/2` da palavra “zero”.

## Centro Green e tilt

O canal Green conserva informação que o readout escalar Genuine não contém.
Seu locus de anulação é o equilíbrio transversal:

```lean
complexifiedAlignedGreenLimitOperator p q s = 0
  ↔ criticalDisplacement s.re = 0.
```

Ao colocar Genuine e Green numa soma direta, o kernel obtém:

```lean
genuineGreenCompletedLimitOperator p q s = 0
  ↔ IsNativeCarryRealOperatorZero 3 s.re s.im ∧
      s.re = (1 : ℝ) / 2.
```

Portanto, num eventual zero off-equilibrium, o primeiro canal continua zero e
o canal Green permanece não nulo. O teorema
`nativeZero_offEquilibrium_channelSeparation` registra os dois fatos na mesma
conclusão. Isso é detecção do tilt, não redefinição do zero.

## Interseção explícita, sem novo tipo de zero

`NativeCarryRealPlaneMassBalancedBoundaryClosesAt` registra a interseção
explícita:

```text
mass compatibility and native zero.
```

Ele pode ser útil quando uma construção exige simultaneamente equilíbrio e
fechamento, mas seu nome e seu tipo não criam uma categoria diferente de zero.

## TFVD, retorno e proveniência

As identidades TFVD permanecem ortogonais à correção semântica:

```lean
carryWeightedVerticalTfvd_identity
```

prova `G_q B_q + R_q Tr_q = I`, e

```lean
nativeGpreFiniteTfvdReconstruction_comp_analysis
```

prova que reconstrução composta com análise é a identidade. Essas camadas
conservam bracket, traço e proveniência sem alterar o significado de zero.

## Auditoria

Para verificar a higiene estática:

```bash
bash scripts/static_audit.sh
```

Para elaborar toda a superfície pública:

```bash
lake build --wfail
```

A correção completa está registrada em
`docs/NATIVE_ZERO_SEMANTICS_CORRECTION.md`.
