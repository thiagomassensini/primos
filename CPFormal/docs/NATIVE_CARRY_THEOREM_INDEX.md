# Índice canônico da teoria nativa do carry

## Escopo congelado

Este índice lê o tronco importado por `CPFormal.lean`, tomando como base o
checkpoint publicado `v0.49.0` e o `main` em
`e4f36c94c5d9208b65f7f603f7966c27d59d851e`.

Na base desse checkpoint:

- 174 arquivos Lean formam a superfície `CPFormal`;
- 37.976 linhas Lean estão no núcleo;
- o índice sintático encontra 2.501 declarações:
  1.638 `theorem`, 773 `def`, 46 `structure`, 34 `abbrev`,
  5 `inductive`, 4 `lemma` e 1 `instance`;
- a auditoria estática encontra zero `axiom`, `sorry` ou `admit`.

Os números são inventário, não argumento matemático. A autoridade de cada
resultado é seu tipo Lean e a elaboração pelo kernel.

Este documento separa:

1. a rota nativa canônica;
2. interfaces equivalentes ou auxiliares;
3. rotas paralelas interrompidas por decisão de pesquisa.

Uma rota paralela não é classificada como barreira. Ela apenas não entra na
dependência do teorema nativo consolidado.

## Ordem canônica

| Camada | Objeto preservado | Declarações centrais | Fonte |
|---|---|---|---|
| Incidência | inteiro, centro, perna e offset | `oddLegEquivIncidence`, `balancedOffsetEquivNonzeroResidue`, `nonmultipleEquivIncidence` | `Carry/C2Adjacent.lean`, `Carry/CpBalancedResidue.lean`, `Carry/CpGlobalIncidence.lean` |
| Profundidade | valuation do centro carregado | `effectiveDepth_eq_centerDepth`, `dvd_sub_iff_eq_offset` | `Carry/C2Depth.lean`, `Carry/CpDepth.lean` |
| Transporte | soma por pernas sem perda de bordo | `weighted_reindex_alignedBox` | `Carry/C2AlignedBox.lean`, `Carry/CpAlignedBox.lean` |
| Massa | custo posicional `b⁻ᵏ` | `criticalMass`, `criticalMass_reindex_alignedBox` | `Carry/CpBranchWeight.lean` |
| Amplitude | raiz quadrática `b⁻ᵏ⧸²` | `criticalAmplitude`, `criticalAmplitude_sq_eq_mass` | `Carry/CpBranchWeight.lean` |
| Rigidez posicional | compatibilidade massa–energia | `branchAmplitude_sq_eq_criticalMass_iff_of_one_lt`, `positionalCarryMassCompatible_iff` | `Analytic/CpPositionalCarryQuadraticRigidity.lean` |
| Estado real | amplitude e rotação separadas | `nativeCarryRealPlaneEnergy_sampleAt`, `nativeCarryRealPlaneMassCompatible_iff` | `Analytic/CpNativeCarryRealPlaneBracket.lean` |
| Bracket | segunda diferença saturada | `centeredSecondDifference`, `saturatedBracket`, `bracket_eq_saturatedBracket` | `Finite/Bracket.lean`, `Genuine/CpBracketPairing.lean` |
| Genuine finito | síntese de sementes e brackets | `finite_genuine_cancellation`, `finiteChart_eq_positiveIntervalSum_sub_p_mul_centerSum` | `Genuine/FiniteCancellation.lean`, `Genuine/CpFiniteChart.lean` |
| TFVD/retorno | bracket mais traço reconstrói o estado | `carryWeightedScalarReconstruction`, `carryWeightedVerticalTfvd_identity` | `Analytic/CpCarryWeightedVerticalTfvdFinite.lean`, `Analytic/CpCarryWeightedVerticalTfvdIdentity.lean` |
| Proveniência | análise injetiva com inversa à esquerda | `nativeGpreFiniteTfvdReconstruction_comp_analysis`, `nativeGpreFiniteTfvdAnalysis_injective` | `Analytic/CpNativeGpreTfvdAnalysis.lean` |
| Fase real | grupo unitário e gerador logarítmico | `finiteRealSpectralStateVector_eq_evolution_zero`, `infiniteRealSpectralGenerator_isSelfAdjoint` | `Analytic/CpNativeCarryLogPhaseOrbit.lean`, `Analytic/CpInfiniteRealSpectralGenerator.lean` |
| Readout nativo | ressonância parametrizada apenas por `t : ℝ` | `IsRealSpectralResonance`, `isRealSpectralResonance_iff_nativeGpreGenuineLimit_zeroCharacteristic` | `Analytic/CpRealSpectralGenerator.lean`, `Analytic/CpNativeGpreTfvdGenuineCompression.lean` |
| Confinamento | zero nativo tem uma única fibra radial | `isNativeCarryRealOperatorZero_iff`, `nativeCarryRealOperatorZero_sigma_eq_half` | `Analytic/CpNativeCarryRealOperatorConfinement.lean` |

## O novo teorema consolidado

O operador real nativo é apresentado por dois dados que já existiam:

```lean
def IsNativeCarryRealOperatorZero
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  NativeCarryRealPlaneMassCompatible sigma time ∧
    NativeCarryRealOperatorBoundaryClosesAt camera sigma time
```

A primeira coordenada é o domínio físico antes do bracket. A segunda é a
observação de que os resultantes reais do bracket fecham. Nenhuma seta
`zero → massa` é pedida: a massa já pertence ao domínio do operador que está
sendo chamado de nativo.

O kernel é solicitado a verificar:

```lean
theorem isNativeCarryRealOperatorZero_iff
    (camera : ℕ) (sigma time : ℝ) :
    IsNativeCarryRealOperatorZero camera sigma time ↔
      sigma = (1 : ℝ) / 2 ∧
        IsNativeCarryRealOperatorResonance camera time
```

Em notação de conjuntos:

\[
Z_{\mathrm{native},\,c}
=
\left\{\frac12\right\}\times\mathcal R_c,
\]

onde `c` é qualquer largura natural de câmera e
\(\mathcal R_c\subseteq\mathbb R\) é o conjunto dos tempos reais em que a
câmera fecha.

Consequências literais:

- o resultado vale para toda câmera, sem hipótese de primalidade;
- a rotação real continua livre;
- cancelamento do bracket decide somente quais tempos pertencem
  a \(\mathcal R_c\);
- o bracket não redefine o expoente radial;
- não existe parâmetro `s : ℂ` no enunciado;
- não existe Zeta, equação funcional ou hipótese externa;
- não existe `bridge`, `certificate`, `hmass` ou `hreconstruct`.

O único argumento recebido pelo corolário de confinamento é um zero do próprio
operador nativo:

```lean
theorem nativeCarryRealOperatorZero_sigma_eq_half
    (hzero : IsNativeCarryRealOperatorZero camera sigma time) :
    sigma = (1 : ℝ) / 2
```

## Dependência formal mínima do confinamento

```text
branchAmplitude b sigma k
        │ energia quadrática
        ▼
branchAmplitude_sq_eq_criticalMass_iff_of_one_lt
        │ realização em R × R
        ▼
nativeCarryRealPlaneMassCompatible_iff
        │ domínio do operador nativo
        ▼
isNativeCarryRealOperatorZero_iff
```

O bracket aparece no predicado de ressonância, mas não é usado para escolher
a casca radial. Isso expressa no tipo Lean a ordem causal da teoria:

```text
carry → massa → amplitude → estado → bracket → zero.
```

## TFVD, retorno e ponta operatorial

A TFVD não é uma tentativa de inverter apenas o stencil. Ela conserva o
complemento de bordo explicitamente:

```lean
carryWeightedVerticalTfvd_identity
```

prova

\[
G_qB_q+R_q\operatorname{Tr}_q=I.
\]

No carrier enriquecido:

```lean
nativeGpreFiniteTfvdReconstruction_comp_analysis
```

prova que reconstrução composta com análise é a identidade. Portanto, bracket,
traço e proveniência permanecem separados e o estado não é tratado como três
amostras livres.

Na ponta do readout:

```lean
isRealSpectralResonance_iff_nativeGpreGenuineLimit_zeroCharacteristic
```

identifica a ressonância real com o valor característico zero do pencil-limite
das compressões nativas. Esse endpoint classifica os tempos em
\(\mathcal R_c\); ele não reabre a coordenada radial já fixada pelo carry.

## Três objetos que não devem ser misturados

| Objeto | Parâmetros | Papel |
|---|---:|---|
| Operador real nativo | `camera : ℕ`, `time : ℝ` | massa fixada antes do bracket; zeros são ressonâncias reais |
| Apresentação radial do operador nativo | `camera`, `sigma`, `time` com compatibilidade de massa no domínio | permite provar que toda apresentação reduz a `sigma = 1/2` |
| Continuação escalar ambiente | parâmetro não real livre | objeto auxiliar mais forte; não é necessário para o confinamento nativo |

O operador completado `Genuine ⊕ Green` também permanece um quarto objeto
distinto. Seus teoremas são válidos, mas não participam da prova
`isNativeCarryRealOperatorZero_iff`.

## Rotas paralelas

As famílias abaixo permanecem formalizadas e disponíveis, mas não são
dependências do novo teorema:

- continuação escalar, tempo não real e exaustão;
- Green cruzado e operador completado;
- boundary relation refletida e Cayley;
- correção angular/Abel;
- Bessel, estado global e domínio de traço;
- sínteses C2–`G_pre` e detectores multibase.

Algumas dessas rotas possuem guardrails de equivalência com alvos escalares
mais fortes. Isso classifica a força lógica de seus enunciados; não transforma
uma interrupção escolhida em impossibilidade matemática.

## Como consultar o índice literal

O root ativo é `CPFormal.lean`. Para localizar uma declaração pelo nome:

```bash
rg -n 'nome_da_declaracao' CPFormal -g '*.lean'
```

Para listar declarações e seus arquivos:

```bash
rg -n '^[[:space:]]*(@\[[^]]+\][[:space:]]*)?(private[[:space:]]+)?(noncomputable[[:space:]]+)?(def|abbrev|structure|theorem|lemma)[[:space:]]' \
  CPFormal -g '*.lean'
```

Para verificar a higiene estática:

```bash
bash scripts/static_audit.sh
```

A promoção final continua sendo feita apenas por:

```bash
lake build --wfail
```

no workflow `Lean kernel audit`.
