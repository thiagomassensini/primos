# Continuação da formalização Lean 4: do operador Genuine–Green ao crosswalk C2–`G_pre`–Bessel

## Dirichlet one-jet, síntese cofinal, rigidez do tilt, identificação com ζ, domínio vertical e defeitos centrados de carry

## 1. Identificação formal e relação com as notas anteriores

Este documento continua, sem substituir, as notas:

1. `FORMALIZACAO_LEAN4_TEORIA_DO_CARRY_AO_OPERADOR_GENUINE(1).md`;
2. `GENUINE_GREEN_COMPLETED_LIMIT_OPERATOR_NE_ZERO_OFF_CRITICAL.md`.

A primeira nota constrói a sequência

$$
\text{carry}
\longrightarrow
\text{massa e amplitude crítica}
\longrightarrow
\text{bracket e Genuine}
\longrightarrow
\text{Green/TFVD/}G_{\mathrm{pre}}
\longrightarrow
\text{operadores no limite}.
$$

A segunda nota fecha a caracterização do operador Genuine–Green completado:

$$
\mathcal C_{p,q}(s)=0
\iff
G(s)=0\ \land\ \operatorname{Re}(s)=\frac12,
$$

mas separa corretamente esse resultado da afirmação mais forte

$$
G(s)=0\Longrightarrow\operatorname{Re}(s)=\frac12.
$$

A presente nota documenta o que foi formalizado depois desse firewall lógico, até o checkpoint em que os readouts Green foram realizados como coeficientes de uma família Bessel aritmética de defeitos centrados de carry.

### Superfície formal do checkpoint matemático

- **Repositório:** `thiagomassensini/primos`;
- **branch:** `agent/connected-c2-tfvd-bridge`;
- **pull request:** PR #8;
- **checkpoint matemático:** `0aa69d55f8425d1f628db6f69ff0812bc583e3b4`;
- **workflow:** `Lean kernel audit` #531;
- **elaboração:** `lake build --wfail`;
- **auditoria estática:** rejeita explicitamente `axiom`, `sorry` e `admit` na superfície `CPFormal`.

A continuação pode ser resumida por

$$
\boxed{
\begin{gathered}
\text{guardas da inclusão de kernels}
\longrightarrow
\text{cumulante C2 e pushforward diádico exato}\\
\longrightarrow
\text{one-jet Dirichlet na TFVD e em }G_{\mathrm{pre}}
\longrightarrow
\text{síntese cofinal tagueada}\\
\longrightarrow
\text{rigidez do tilt e identificação }G=\zeta\\
\longrightarrow
\text{bulk Green como momento, traço e readout log-jet}\\
\longrightarrow
\text{Bessel explícita dos defeitos centrados de carry}.
\end{gathered}
}
$$

## 2. A ponte final foi isolada antes das novas construções

O enunciado escalar forte foi nomeado por

```lean
def GenuineStrongNonvanishingInStrip : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
    s.re ≠ (1 : ℝ) / 2 →
      genuineContinuation s ≠ 0
```

O módulo

```text
CPFormal/Analytic/CpGenuineGreenKernelInclusion.lean
```

define formulações globais da seta ainda ausente:

```text
GenuineKernelIncludedInGreenLimitKernel
GenuineKernelSynchronizesGreenLimitCoordinates
GenuineKernelSynchronizesTfvdProvenance
GenuineKernelHasTfvdProvenanceZeroCofinalReindex
GenuineKernelClosesCompletedLimitOperator.
```

Para câmeras primas distintas, o Lean prova que são equivalentes entre si e ao enunciado escalar forte. Entre os teoremas centrais estão:

```text
genuineKernelIncludedInGreenLimitKernel_iff_coordinates
genuineKernelIncludedInGreenLimitKernel_iff_tfvdProvenance
genuineKernelIncludedInGreenLimitKernel_iff_tfvdProvenanceZeroCofinalReindex
genuineKernelIncludedInGreenLimitKernel_iff_completedOperator
genuineKernelIncludedInGreenLimitKernel_iff_primeGreenState
genuineKernelIncludedInGreenLimitKernel_iff_saturatesCarry
genuineKernelIncludedInGreenLimitKernel_iff_strongNonvanishing.
```

Em forma lógica:

$$
\boxed{
\begin{aligned}
&\text{inclusão do kernel Genuine no Green}\\
&\iff\text{sincronização Green}\\
&\iff\text{sincronização da proveniência TFVD}\\
&\iff\text{existência de estado multiprima no kernel}\\
&\iff\text{saturação do carry}\\
&\iff\text{não-anulação forte off-critical}.
\end{aligned}
}
$$

Essas equivalências são guardas de escopo. Nenhuma das proposições globais acima é declarada como instância.

## 3. Carrier local de Tate e bracket radial crítico

O módulo

```text
CPFormal/Analytic/CpTateCarryLocalCarrier.lean
```

formaliza apenas o dicionário local do caráter não ramificado trivial. A razão local é

$$
r_p(s)=p^{-s},
$$

e a casca de profundidade $k$ é $r_p(s)^k$.

Os teoremas

```text
tateUnramifiedLocalRatio_ne_zero
norm_tateUnramifiedLocalRatio_eq_branchAmplitude
norm_tateUnramifiedLocalRatio_eq_primeCarryAmplitudeRatio
```

provam

$$
\|p^{-s}\|=p^{-\operatorname{Re}(s)},
$$

e, na meia-abscissa,

$$
\|p^{-s}\|=p^{-1/2}=\operatorname{primeCarryAmplitudeRatio}(p).
$$

A torre geométrica está no kernel do bracket cujo peso acompanha o próprio carrier:

```text
tateUnramifiedValuationShell_firstDifference_eq_zero
tateUnramifiedValuationShell_secondDifference_eq_zero.
```

Seu traço inicial é $(1,0)$, por `tateUnramifiedValuationShell_initialTrace`.

A covariância por dressing diagonal é formalizada por:

```text
carryWeightedScalarFirstDifference_phaseDress
carryWeightedScalarSecondDifference_phaseDress
carryWeightedScalarTrace_phaseDress
carryWeightedScalarGreenSum_phaseDress.
```

Se um bracket de peso $q$ atua numa torre de razão $r$, então

$$
B_q(r^k)=q^{-1}r^k(r-q)^2.
$$

Nome Lean:

```text
carryWeightedScalarSecondDifference_geometricMismatch.
```

Consequentemente,

$$
\boxed{
B_{p^{-1/2}}\bigl((p^{-\sigma})^k\bigr)|_{k=0}=0
\iff
\sigma=\frac12.
}
$$

Nome Lean: `primeCarryCriticalBracket_radialShell_zero_iff`.

O módulo `CpCriticalRadialBracketGuard.lean` prova que promover esse fechamento local a todo zero Genuine é equivalente ao teorema forte:

```text
genuineKernelClosesCriticalRadialBracket_iff_strongNonvanishing.
```

## 4. Cumulante conectado C2 e Richardson

No módulo

```text
CPFormal/Analytic/CpConnectedC2Defect.lean
```

consideram-se massas deformadas

$$
a_h(p)=1-h\varepsilon_p,
\qquad
a_h(q)=1-h\varepsilon_q,
\qquad
a_h(pq)=1-h\varepsilon_{pq},
$$

e o cumulante

$$
K_h=a_h(pq)-a_h(p)a_h(q).
$$

As definições são `c2PairConnectedCumulant` e `c2PairRichardsonDefect`. O Lean prova

$$
\boxed{
2K_{1/2}-K_1
=
\frac12\varepsilon_p\varepsilon_q.
}
$$

Nome Lean: `c2PairRichardsonDefect_eq`.

O termo conjunto $\varepsilon_{pq}$ e todos os termos lineares cancelam exatamente. A independência do termo conjunto é `c2PairRichardsonDefect_independent_of_joint`.

Foi também definido o detector radial-modelo

$$
\operatorname{C2Rad}_{p,q}(\delta)
=
\frac12R_p(\delta)R_q(\delta),
$$

com fatoração

$$
\operatorname{C2Rad}_{p,q}(\delta)
=
2\delta^2C_p(\delta)C_q(\delta).
$$

Os teoremas

```text
crossPrimeRadialC2Detector_eq_delta_sq_factor
crossPrimeRadialC2Detector_pos
crossPrimeRadialC2Detector_eq_zero_iff
```

mostram que, para bases primas,

$$
\operatorname{C2Rad}_{p,q}(\delta)=0\iff\delta=0.
$$

Essa especialização não identifica o defeito aritmético C2 com `cpRadialDifference`.

O defeito cross-prime antigo não ganha conectividade pela combinação $L\mapsto2L$:

```text
crossPrimeAlignedCutoffDefect_richardson_eq_self.
```

A hipótese `GenuineKernelClosesRadialC2Detector` é protegida por

```text
genuineKernelClosesRadialC2Detector_iff_strongNonvanishing.
```

## 5. Porta TFVD do cumulante conectado

O módulo

```text
CPFormal/Analytic/CpConnectedC2TfvdPort.lean
```

prova que

$$
K_h
=
\operatorname{sameSEdgeBoundaryWedge}
\bigl(a_h(p),a_h(pq),1,a_h(q)\bigr).
$$

As quatro massas são codificadas por `c2MassTfvdValueCoordinate` e `c2MassTfvdJetCoordinate`. Depois da decodificação:

$$
\boxed{
\operatorname{visibleCell}=K_h,
\qquad
\operatorname{dormantCell}=0.
}
$$

Nomes Lean:

```text
c2MassTfvdBoundaryCells_eq
c2MassTfvdBoundaryCells_visible_eq
c2MassTfvdBoundaryCells_total_eq.
```

Richardson pode ser aplicado depois da codificação:

```text
c2MassTfvdBoundaryCells_richardson_eq
c2MassTfvdBoundaryCells_total_richardson_eq.
```

A forma bilinear do wedge é essencial. O módulo `CpNativeGpreConnectedC2Guard.lean` prova que o canal Jordan nativo de `G_pre` é multiplicativo e, portanto, possui cumulante misto nulo em entradas coprimas. Também prova que nenhum funcional puramente linear sobre apenas o par de marginais representa universalmente o produto conectado:

```text
nativeGpreJordanPairConnectedCumulant_distinct_primes
no_linear_pair_readout_realizes_connected_product.
```

## 6. Pushforward concreto do ramo ímpar C2

O arquivo

```text
CPFormal/Carry/C2OddCorePushforward.lean
```

formaliza as duas fibras

$$
2^km-1,
\qquad
2^km+1,
\qquad k\ge2,
$$

com peso $2^{-k}$. Os últimos níveis admissíveis são calculados separadamente por `oddCoreMinusDepth` e `oddCorePlusDepth`.

A massa truncada concreta é

```text
oddCoreTruncatedMass cutoff m.
```

O passo de $4M$ para $8M$ acrescenta exatamente um nível em cada ramo:

```text
oddCoreMinusDepth_eight_mul_eq_four_mul_add_one
oddCorePlusDepth_eight_mul_eq_four_mul_add_one.
```

A recorrência finita é derivada, não assumida:

$$
a_{8M}(m)=\frac12+\frac12a_{4M}(m).
$$

Nome Lean: `oddCoreTruncatedMass_eight_mul_eq`.

Logo,

$$
\boxed{
2a_{8M}(m)-a_{4M}(m)=1
}
$$

para $0<m\le M$. Nome Lean: `oddCoreTruncatedMass_richardson_exact`.

## 7. Cumulante concreto e extração logarítmica

O módulo

```text
CPFormal/Analytic/CpC2OddCorePushforwardTfvd.lean
```

define

$$
K_T(p,q)=a_T(pq)-a_T(p)a_T(q).
$$

O Richardson concreto satisfaz

$$
\boxed{
2K_{8M}(p,q)-K_{4M}(p,q)
=
\frac12\varepsilon_{M,p}\varepsilon_{M,q},
}
$$

onde $\varepsilon_{M,r}=1-a_{4M}(r)$.

Nomes Lean:

```text
c2OddCoreConnectedCumulant_richardson_exact
c2OddCoreConnectedCumulantReal_richardson_exact.
```

A porta TFVD concreta preserva exatamente o cumulante:

```text
c2OddCoreMassTfvdBoundaryCells_eq
c2OddCoreMassTfvdBoundaryCells_richardson_exact.
```

Para a extração logarítmica, a semente é normalizada por $a_T(1)=1$, e define-se $b_T$ pela inversão de Dirichlet:

```text
c2OddCoreLogCoefficientArithmetic
c2OddCoreLogCoefficientArithmetic_mul_mass.
```

Para primos ímpares distintos:

$$
\boxed{
b_T(pq)=\log(pq)K_T(p,q).}
$$

Nome Lean: `c2OddCoreLogCoefficient_distinct_primes`.

A correção dyádica do coeficiente semiprimo é `c2OddCoreLogCoefficient_distinct_primes_richardson_exact`.

## 8. Lift sem perda do prefixo log-jet para `G_pre`

O módulo

```text
CPFormal/Analytic/CpC2LogJetGpreLift.lean
```

mantém os primeiros $N$ gradientes log-Dirichlet como um estado finitamente suportado:

```text
c2LogJetPrefixCore s N.
```

A soma telescópica recupera o vértice log-Dirichlet:

```text
c2LogJetPrefixCore_sum_eq
positiveLogDirichletValue_eq_sum_range_gradient.
```

O estado entra na análise enriquecida por

```text
c2LogJetPrefixEnrichedAnalysis.
```

A reconstrução TFVD é um left inverse exato:

```text
c2LogJetPrefixEnrichedAnalysis_reconstruction
c2LogJetPrefixEnrichedReadout_analysis.
```

As pernas de proveniência são preenchidas pelo mesmo estado não sintetizado:

```text
c2LogJetPrefixEnrichedAnalysis_provenance_value
c2LogJetPrefixEnrichedAnalysis_numberFlux_eq_level_mul_value.
```

O semiprime possui ainda o crosswalk finito

```text
positiveLogDirichletValue_product_eq_logScales_add_commutators.
```

Sob o bloco primo, o wedge `same-s` ganha o quadrado do autovalor ordinário; após a normalização de fase, resta o fator radial real $p^{-2\delta}$:

```text
cpLogJetSameSBlockWedge_eq_eigenvalue_sq_mul
phaseNormalizedCpLogJetSameSBlockWedge_eq_radial_sq_mul.
```

O coeficiente conectado decai geometricamente:

$$
\varepsilon_{2M,r}=\frac12\varepsilon_{M,r},
\qquad
C2_{2M}=\frac14C2_M.
$$

Nomes Lean:

```text
c2OddCoreFourScaleDefect_two_mul_eq_half
c2OddCoreConnectedRichardsonDefect_two_mul_eq_quarter.
```

## 9. Injeção do one-jet Dirichlet na TFVD

O módulo

```text
CPFormal/Analytic/CpC2DirichletJetTfvd.lean
```

eleva cada massa ao one-jet

$$
D_T(m,s)=a_T(m)m^{-s},
\qquad
L_T(m,s)=a_T(m)\log(m)m^{-s}.
$$

Como $D_T(1,s)=1$ e $L_T(1,s)=0$, o canal logarítmico precisa usar a regra de Leibniz em duas células. O kernel prova

$$
L(pq,s)=L(p,s)D(q,s)+D(p,s)L(q,s).
$$

Nome Lean: `natLogDirichletTerm_mul_leibniz`.

O wedge ordinário produz

$$
\boxed{
W_D(T;p,q,s)=K_T(p,q)(pq)^{-s}.
}
$$

A derivada logarítmica do determinante é

$$
\begin{aligned}
W_{\log}(T;p,q,s)
={}&W(L_p,L_{pq};D_1,D_q)\\
&+W(D_p,D_{pq};L_1,L_q),
\end{aligned}
$$

e o Lean prova

$$
\boxed{
W_{\log}(T;p,q,s)
=K_T(p,q)\log(pq)(pq)^{-s}
=b_T(pq)(pq)^{-s}.
}
$$

Teoremas centrais:

```text
c2OddCoreDirichletSpectralGap_eq_connectedCumulant_mul
c2OddCoreDirichletLogSpectralGap_eq_connectedCumulant_mul
c2OddCoreDirichletLogSpectralGap_eq_logCoefficient_mul
c2OddCoreDirichletLogTfvdReadout_eq_spectralGap
c2OddCoreDirichletLogTfvdReadout_eq_logCoefficient_mul.
```

Richardson continua exato depois da injeção espectral e da codificação TFVD:

```text
c2OddCoreDirichletLogSpectralGap_richardson_exact
c2OddCoreDirichletLogTfvdReadout_richardson_exact.
```

## 10. Leitura nas tags e normalização cofinal

O módulo

```text
CPFormal/Analytic/CpC2DirichletJetGpre.lean
```

coloca as quatro pernas espectrais nas coordenadas enriquecidas. O readout

```text
c2GpreNormalizedProvenanceValueReadout
```

usa somente a perna de valor de `G_pre` e divide pelo coeficiente nativo da própria tag ativa. Nenhuma reconstrução TFVD participa dessa leitura.

Um atlas `C2GpreActiveSpectralAtlas` mantém tags para as células

$$
p,\quad pq,\quad1,\quad q.
$$

O kernel recupera os pares ordinários e logarítmicos e prova que o readout de proveniência coincide com o gap espectral local.

A escala conectada é

$$
C2_M(p,q)=\frac12\varepsilon_M(p)\varepsilon_M(q).
$$

A razão cofinal é

$$
\operatorname{NormalizedLocalReadout}_M
=
\frac{2\operatorname{Readout}_{8M}-\operatorname{Readout}_{4M}}{C2_M(p,q)}.
$$

No locus onde o denominador é não nulo:

$$
\boxed{
\operatorname{NormalizedLocalReadout}_M(p,q,s)
=
\log(pq)(pq)^{-s}.
}
$$

Nome Lean:

```text
c2OddCoreNormalizedCofinalGpreReadout_eq_natLogDirichletTerm.
```

Assim, o decaimento $C2_{2M}=C2_M/4$ é removido exatamente. Uma célula semiprima fixa não tende a zero em um zero Genuine; ela estabiliza no átomo log-Dirichlet.

## 11. Síntese cofinal full-support e igualdade com o gap horizontal

Os módulos

```text
CPFormal/Analytic/CpC2GpreCofinalSynthesis.lean
CPFormal/Analytic/CpC2GpreCofinalTaggedSynthesis.lean
```

estendem o átomo ao suporte multiplicativo completo:

$$
A_n(s)=\log(n)n^{-s}.
$$

No suporte semiprimo, ele coincide com o readout C2 normalizado. Para uma câmera prima $r$, o peso

$$
w_r(m)=\frac{r}{\log(rm)}
$$

remove o gerador logarítmico:

$$
\boxed{
w_r(m)A_{rm}(s)=r(rm)^{-s}.}
$$

A síntese de uma câmera satisfaz

$$
\boxed{
\operatorname{Syn}_{r,M}(s)
=r^{1-s}P_M(s).
}
$$

Nome Lean: `c2GpreNormalizedCameraPrefixSynthesis_eq_weightedPrefix`.

Uma família `C2GpreActiveCofinalAtlasFamily` permite que o atlas de tags cresça com o cutoff. A síntese tagueada é definida antes de mencionar o gap e o kernel prova, em cada escala,

$$
\boxed{
\operatorname{TaggedSyn}_L(p,q,s)
=
\operatorname{CameraGap}_L(p,q,s).
}
$$

Teoremas:

```text
c2GpreNormalizedCofinalTaggedSynthesis_eq_atomSynthesis
c2GpreNormalizedCofinalTaggedSynthesis_eq_cameraGap
c2GpreNormalizedCofinalTaggedSynthesis_error_tendsto_zero
c2GpreNormalizedCofinalTaggedSynthesis_intertwinesCameraGap.
```

O erro é identicamente zero. Em um zero Genuine:

```text
c2GpreNormalizedCofinalTaggedSynthesis_tendsto_zero_of_genuine_zero.
```

Esse fechamento é horizontal e oscilatório; não é ainda fechamento Green.

## 12. Compressão rank-one versus energia Green

O módulo

```text
CPFormal/Analytic/CpC2GpreGreenActivationGuard.lean
```

mantém as duas câmeras separadas antes da subtração. A síntese horizontal é a compressão

$$
(z_p,z_q)\longmapsto z_p-z_q.
$$

O par $(1,1)$ possui compressão zero, mas energia quadrática positiva, mesmo depois de inserir as amplitudes críticas.

Teoremas:

```text
c2GpreCameraPairCompression_zero_with_positive_carryEnergy
c2GpreCameraPairCompression_not_carryEnergy_coercive
c2GpreNormalizedCofinalTaggedSynthesis_eq_pairCompression.
```

As afirmações

```text
C2GpreTaggedSynthesisActivatesGreenClosure
C2GpreTaggedSynthesisActivatesCarrySaturation
```

são ambas equivalentes à não-anulação forte:

```text
c2GpreTaggedSynthesisActivatesGreenClosure_iff_strongNonvanishing
c2GpreTaggedSynthesisActivatesCarrySaturation_iff_strongNonvanishing
c2GpreTaggedGreenActivation_iff_carrySaturationActivation.
```

Portanto, a energia deve ser preservada antes da compressão escalar.

## 13. Identificação canônica do Genuine com a zeta de Riemann

O módulo

```text
CPFormal/Analytic/CpGenuineRiemannZetaIdentification.lean
```

fecha a identificação espectral que as notas anteriores ainda tratavam como ponte adicional.

No semiplano $\operatorname{Re}(s)>1$:

```text
genuineDirichlet_eq_riemannZeta.
```

O fator da câmera possui zero removível em $s=1$. O módulo usa o divided slope

```text
cpChartFactorSlope
```

e a regularização inteira `riemannZeta₁` para definir

```text
riemannCpChart p s.
```

A unicidade da continuação analítica fornece

```text
bracketedDirichletChart_eq_riemannCpChart.
```

Como o fator da câmera não zera no strip:

$$
\boxed{
\operatorname{genuineContinuation}(s)=\operatorname{riemannZeta}(s),
\qquad0<\operatorname{Re}(s)<1.
}
$$

Nome Lean: `genuineContinuation_eq_riemannZeta`.

A conjugação e a equação funcional dão a reflexão dos zeros:

```text
genuineContinuation_reflectedParameter_eq_zero_of_zero.
```

Logo a função formal do Genuine no strip é literalmente a zeta de Riemann da Mathlib, não apenas uma função com coeficientes aparentados.

## 14. Rigidez do tilt antes da compressão de fase

O módulo

```text
CPFormal/Analytic/CpGenuineTiltPhaseCancellation.lean
```

remove de cada bloco seu carrier crítico antes de somar:

$$
\widetilde T_k(s)
=
\frac{T_k(s)}{c_k^{-1/2-it}}.
$$

O carrier é não nulo e o kernel prova

$$
\widetilde T_k(s)=\Theta_{3,\delta(s)}(c_k).
$$

Nomes Lean:

```text
canonicalCriticalTiltCarrier_ne_zero
canonicalPhaseUnwoundTiltBlock_eq.
```

Assim, todos os blocos desgirados possuem o mesmo sinal. Para todo cutoff não vazio e $\operatorname{Re}(s)>0$:

$$
\boxed{
\operatorname{UnwoundTiltTrace}_M(s)=0
\iff
\operatorname{Re}(s)=\frac12.
}
$$

Nome Lean: `finiteCanonicalPhaseUnwoundTiltTrace_eq_zero_iff_re_eq_half`.

Para a soma complexa original, o Lean formaliza o critério suficiente:

```text
finiteCanonicalCriticalWeightedTiltTrace_ne_zero_of_first_dominates.
```

Se o primeiro bloco domina a soma das normas da cauda, nenhuma disposição de fases produz zero.

## 15. Cotas quantitativas do tilt

O módulo

```text
CPFormal/Analytic/CpGenuineTiltQuantitativeDomination.lean
```

prova versões afiadas da estimativa de segunda diferença. Um lower bound simétrico para

$$
f''(c-t)+f''(c+t)
$$

produz o lower bound correspondente para o stencil, preservando a constante quadrática exata. A versão superior é paralela.

Nomes Lean:

```text
centeredSecondDifference_ge_of_pair_secondDeriv_ge
centeredSecondDifference_le_of_pair_secondDeriv_le.
```

O módulo `CpGenuineTiltBlockBounds.lean` aplica isso a $x^{-\delta}$ na câmera canônica $p=3$. Para

$$
-\frac12<\delta<\frac12,
\qquad\delta\ne0,
\qquad c>1,
$$

o kernel prova

$$
\boxed{
|\delta(\delta+1)|c^{-\delta-2}
\le
|\Theta_{3,\delta}(c)|
\le
|\delta(\delta+1)|(c-1)^{-\delta-2}.
}
$$

Nomes Lean:

```text
abs_cpTilt_three_lower_bound
abs_cpTilt_three_upper_bound.
```

O módulo `CpGenuineTiltTailDomination.lean` transporta essas cotas para os blocos complexos e prova

$$
\|c^{-1/2-it}\|=c^{-1/2}.
$$

A altura altera apenas a direção, não o comprimento.

O módulo `CpGenuineTiltAuxiliaryRoute.lean` mantém como rota auxiliar:

```text
CanonicalCriticalTiltFirstBlockDominatesAt
CanonicalCriticalCarrierRemainderProjectionPositiveAt
finiteCanonicalBracketTrace_ne_zero_of_remainderProjectionPositive
finiteCanonicalBracketTrace_ne_zero_of_remainder_norm_lt_tilt.
```

Nenhum desses certificados é declarado globalmente.

## 16. Bulk Green como momento e como readout log-jet

O módulo

```text
CPFormal/Analytic/CpGenuineGprePrimeMomentCrosswalk.lean
```

realiza o bulk Green da câmera $p$ como momento de um único estado de energia, independente da câmera, contra o gap de perfis refletidos de primeira camada:

$$
\boxed{
\left\langle
\rho_{p,1-\sigma}-\rho_{p,\sigma},
X_{M,s}
\right\rangle
=
\operatorname{GreenBulk}_{p,M}(s).
}
$$

Nome Lean:

```text
inner_nativeGpreReflectedFirstLevelGapProfile_eq_greenBulk.
```

A passagem dessa família espectral móvel para os perfis nativos fixos $\rho_{p,1}$ é nomeada por

```text
NativeGpreReflectedGapHasFixedTimeMomentStateAt.
```

Para cutoff não vazio:

```text
nativeGpreReflectedGapHasFixedTimeMomentStateAt_iff_critical.
```

A promoção em todo zero Genuine é protegida por

```text
genuineZerosProduceNativeGpreFixedTimeMomentCrosswalk_iff_strongNonvanishing.
```

Independentemente, o módulo

```text
CPFormal/Analytic/CpGenuineGpreLogJetGreenBulkReadout.lean
```

soma a identidade local

$$
W_n^{\mathrm{comm}}(s)=-\log(p)W_n^G(s),
$$

divide por $-\log p$ e insere a amplitude crítica $p^{-1/2}$. O resultado é

$$
\boxed{
\operatorname{LogJetGreenReadout}_{p,M}(s)
=
\operatorname{GreenBulk}_{p,3M}(s).
}
$$

Nomes Lean:

```text
finiteNativeGpreLogJetGreenBulkReadout_eq
finiteEnrichedNativeGpreLogJetGreenBulkReadout_eq.
```

A segunda identidade é formada diretamente das coordenadas TFVD enriquecidas, preservando as três pernas até depois do wedge.

## 17. Massa, upgrade de amplitude e traço vertical

O módulo

```text
CPFormal/Analytic/CpGenuineGprePrimeAmplitudeUpgrade.lean
```

separa duas escalas:

- o perfil de massa, vestido por $p^{-1}$;
- o perfil Green crítico, vestido por $p^{-1/2}$.

A relação é

$$
\operatorname{MassGreen}_p(s)
=
p^{-1/2}\operatorname{GreenBulk}_p(s).
$$

O perfil de massa é quadrado-somável em todo o strip:

```text
summable_primeMassGreenBulkCutoffProfile_sq.
```

O upgrade multiplica por $\sqrt p$:

```text
primeAmplitudeUpgrade_massBulk_eq_carryBulk.
```

Seu domínio é `PrimeAmplitudeUpgradeDomain`, e o limiar exato é

```text
primeMassGreenBulkCutoffProfile_mem_upgradeDomain_iff.
```

Para cutoff não vazio:

$$
\boxed{
\operatorname{MassGreen}(s)\in\operatorname{Dom}(\sqrt p)
\iff
\operatorname{Re}(s)=\frac12.
}
$$

O módulo `CpGenuineGprePrimeAmplitudeGraph.lean` expressa o upgrade como relação de grafo Hilbert e como uniformidade de atlas finitos:

```text
exists_primeAmplitudeUpgradeGraphPair_massState_iff
primeAmplitudeUpgradedMassFiniteStatesBounded_iff.
```

O módulo

```text
CPFormal/Analytic/CpGenuineGprePrimeVerticalTraceGate.lean
```

mostra que o upgrade não é um multiplicador artificial. Colocando o perfil de massa no nível vertical $1$:

$$
\operatorname{Tr}_{p^{-1/2}}(m_pe_1)
=
(0,\sqrt p\,m_p).
$$

Para o estado Green:

$$
\boxed{
\operatorname{Tr}_{p^{-1/2}}
\bigl(\operatorname{MassGreen}_p(s)e_1\bigr)
=
\bigl(0,\operatorname{GreenBulk}_p(s)\bigr).
}
$$

Nomes Lean:

```text
primeCarryWeightedVerticalTrace_massFiber
primeMassGreenVerticalTraceFluxProfile_eq
primeMassGreenVerticalGlobalTraceDomainAt_iff.
```

A regularidade global do traço em todo zero Genuine é protegida por

```text
genuineZerosLieInPrimeVerticalTraceDomain_iff_strongNonvanishing.
```

## 18. Atlas, testes duais e perda exata de meia amplitude

O módulo `CpGenuineGprePrimeVerticalTraceAtlas.lean` prova que três atlas finitos são literalmente o mesmo vetor:

$$
\boxed{
\text{fluxos dos traços verticais}
=
\text{bulk Green}
=
\text{readouts log-jet enriquecidos}.
}
$$

Teoremas:

```text
primeMassGreenVerticalTraceFiniteState_eq_greenBulkFiniteState
canonicalEnrichedGpreLogJetGreenAtlasState_eq_verticalTraceFiniteState
canonicalEnrichedGpreLogJetGreenAtlasesBounded_iff.
```

O módulo `CpGenuineGprePrimeVerticalTraceDualTest.lean` transforma a uniformidade vetorial numa Bessel escalar:

```text
CanonicalEnrichedGpreLogJetGreenScalarTestsBounded
canonicalEnrichedGpreLogJetGreenScalarTestsBounded_iff_atlasesBounded
canonicalEnrichedGpreLogJetGreenScalarTestsBounded_iff.
```

A obrigação final torna-se uma cota, uniforme no atlas $S$,

$$
\left|
\sum_{p\in S}c_pR_p(s)
\right|^2
\le
C_s\sum_{p\in S}c_p^2.
$$

O módulo `CpGenuineGprePrimeVerticalTraceWeightedBessel.lean` prova a estimativa disponível sem hipótese de zero:

$$
\boxed{
\left|
\sum_{p\in S}c_pR_p(s)
\right|^2
\le
C_{M,s}
\sum_{p\in S}p\,c_p^2.
}
$$

Nome Lean:

```text
canonicalEnrichedGpreLogJetGreenScalarTest_sq_le_primeWeighted.
```

A perda é exatamente uma meia amplitude, pois

$$
(p^{-1/2})^{-2}=p.
$$

A melhoria não ponderada em todo zero é nomeada por

```text
GenuineZeroProvidesPrimeHalfAmplitudeSmoothing
```

e protegida por

```text
genuineZeroProvidesPrimeHalfAmplitudeSmoothing_iff_strongNonvanishing.
```

## 19. No-go para uma prova puramente vertical

O módulo

```text
CPFormal/Analytic/CpGenuineGprePrimeVerticalTraceNoGo.lean
```

constrói uma família explícita com massa $1/p$ no primeiro nível de cada fibra prima.

A entrada possui energia

$$
\sum_p\frac1{p^2}<\infty.
$$

Seu bracket vertical também é quadrado-somável. Porém o traço produz

$$
\sqrt p\frac1p=\frac1{\sqrt p},
$$

e a energia da saída é

$$
\sum_p\frac1p,
$$

que diverge.

O teorema central é

```text
exists_global_primeVertical_state_and_bracket_without_trace.
```

Portanto,

$$
\text{estado global em }\ell^2
+
\text{bracket global em }\ell^2
\not\Longrightarrow
\text{domínio do traço global}.
$$

O ganho ausente precisa usar a proveniência aritmética específica do zero Genuine.

## 20. Bessel explícita dos defeitos centrados de carry

O módulo

```text
CPFormal/Analytic/CpPrimeCarryDefectBessel.lean
```

parte do pulso adimensional de carry em um ciclo primo:

$$
c_p(a)=\mathbf1_{a=0}.
$$

O defeito centrado é

$$
\phi_p(a)=1-p\mathbf1_{a=0}.
$$

O Lean prova

$$
\sum_{a\bmod p}\phi_p(a)=0,
$$

$$
\boxed{
\sum_{a\bmod p}\phi_p(a)^2=p(p-1).
}
$$

Nomes Lean:

```text
sum_primeCarryResiduePulse_eq_one
sum_primeCenteredCarryDefect_eq_zero
sum_sq_primeCenteredCarryDefect.
```

A normalização probabilística do ciclo fornece $p^{-1/2}$, e a amplitude crítica fornece outro $p^{-1/2}$. O coeficiente total é $p^{-1}$.

O eixo material é

$$
\psi_p(a)=p^{-1}\phi_p(a).
$$

Sua norma é

$$
\boxed{
\|\psi_p\|^2=\frac{p-1}{p}<1.
}
$$

Nome Lean: `primeCriticalCenteredCarryAxis_norm_sq`.

Mantendo as câmeras em coordenadas ortogonais, a síntese satisfaz a Bessel não ponderada:

$$
\boxed{
\left\|
\sum_{p\in S}c_p\psi_p
\right\|^2
\le
\sum_{p\in S}c_p^2.
}
$$

Nome Lean: `finitePrimeCarryDefectSynthesis_norm_sq_le`.

Essa família é aritmética, finita e não usa zero Genuine, fechamento Green ou localização crítica.

## 21. Crosswalk dos readouts Green para os eixos centrados

O módulo do checkpoint atual é

```text
CPFormal/Analytic/CpPrimeCarryDefectReadoutCrosswalk.lean
```

O eixo dual canônico é

$$
\widetilde\psi_p
=
\frac{p}{p-1}\psi_p.
$$

O kernel prova

$$
\boxed{
\langle\psi_p,\widetilde\psi_p\rangle=1,
}
$$

$$
\boxed{
1
\le
\|\widetilde\psi_p\|^2
=
\frac{p}{p-1}
\le2.
}
$$

Nomes Lean:

```text
inner_primeCriticalCenteredCarryAxis_dualAxis
primeCriticalCenteredCarryDualAxis_norm_sq
one_le_primeCriticalCenteredCarryDualAxis_norm_sq
primeCriticalCenteredCarryDualAxis_norm_sq_le_two.
```

Para cada câmera, define-se o estado de proveniência local

$$
X_{p,M,s}
=
R_{p,M}(s)\widetilde\psi_p,
$$

onde $R_{p,M}(s)$ é o readout log-jet enriquecido já definido independentemente.

O Lean prova

$$
\boxed{
\langle\psi_p,X_{p,M,s}\rangle
=
R_{p,M}(s)
=
\operatorname{GreenBulk}_{p,3M}(s).
}
$$

Teoremas:

```text
inner_primeCriticalCenteredCarryAxis_provenanceState
inner_primeCriticalCenteredCarryAxis_provenanceState_eq_greenBulk.
```

No Hilbert global dependente

$$
\ell^2\!\left(
 p\in\mathbb P;
 \operatorname{PrimeCarryResidueHilbert}(p)
\right),
$$

constrói-se, para cada atlas finito $S$,

$$
X_{M,s,S}
=
\sum_{p\in S}R_{p,M}(s)\widetilde\psi_p.
$$

Toda câmera ativa lê sua própria coordenada do mesmo estado comum:

```text
inner_globalCarryAxis_canonicalProvenanceState
inner_globalCarryAxis_canonicalProvenanceState_eq_greenBulk.
```

A Bessel de análise é

$$
\boxed{
\sum_{p\in S}
|\langle\psi_p,x\rangle|^2
\le
\|x\|^2.
}
$$

Nome Lean:

```text
sum_sq_inner_primeCriticalCenteredCarryGlobalAxis_le_norm_sq.
```

Aplicada ao estado canônico, ela e a cota dos eixos duais fornecem o ledger de duas faces:

$$
\boxed{
\sum_{p\in S}|R_{p,M}(s)|^2
\le
\|X_{M,s,S}\|^2
\le
2\sum_{p\in S}|R_{p,M}(s)|^2.
}
$$

Nomes Lean:

```text
sum_sq_enrichedGreenReadout_le_provenanceState_norm_sq
canonicalProvenanceState_norm_sq_le_two_mul_sum_sq_readout.
```

Portanto, uniformidade dos estados comuns e uniformidade dos atlas Green são equivalentes:

```text
canonicalEnrichedPrimeCarryDefectProvenanceStatesBounded_iff_greenAtlasesBounded.
```

Para cutoff não vazio, essa uniformidade seleciona exatamente a meia-abscissa:

```text
canonicalEnrichedPrimeCarryDefectProvenanceStatesBounded_iff.
```

## 22. Checkpoint atual e obrigação remanescente

No nível finito, as seguintes descrições estão exatamente identificadas:

$$
\boxed{
\begin{aligned}
&\text{readout do comutador log-jet enriquecido}\\
&=\text{bulk Green primo}\\
&=\text{fluxo do traço vertical do estado de massa}\\
&=\text{coeficiente contra o eixo centrado de carry}\\
&=\text{coordenada do estado comum de proveniência no atlas}.
\end{aligned}
}
$$

A Bessel dos eixos centrados é não ponderada. O estado comum existe em todo atlas finito. Sua norma é quantitativamente equivalente ao ledger dos readouts Green.

A obrigação ainda aberta é derivar de um zero Genuine uma cota uniforme no atlas:

$$
\boxed{
G(s)=0
\Longrightarrow
\exists C_s\ \forall S,
\qquad
\|X_{1,s,S}\|^2\le C_s.
}
$$

Equivalentemente:

$$
G(s)=0
\Longrightarrow
\left|
\sum_{p\in S}c_pR_p(s)
\right|^2
\le
C_s\sum_{p\in S}c_p^2.
$$

Se essa cota for provada, a cadeia já formalizada fornece

$$
G(s)=0
\Longrightarrow
\sum_p|\operatorname{GreenBulk}_p(s)|^2<\infty
\Longrightarrow
\operatorname{Re}(s)=\frac12.
$$

## 23. Estado lógico exato

### 23.1. Kernel-checked

- equivalências das formulações globais da ponte com a não-anulação forte;
- carrier local, dressing e mismatch quadrático do bracket;
- cumulante C2 e Richardson conectado;
- porta TFVD estática do cumulante;
- pushforward concreto $4M/8M$;
- coeficiente logarítmico semiprimo;
- lift sem perda do prefixo log-jet para `G_pre`;
- one-jet Dirichlet e regra de Leibniz;
- leitura direta das quatro pernas nas tags de proveniência;
- normalização exata pela massa conectada;
- síntese cofinal full-support e igualdade com o gap horizontal;
- erro de síntese identicamente zero;
- guardrail rank-one versus energia Green;
- identificação `genuineContinuation = riemannZeta` no strip;
- reflexão de zeros;
- detector de tilt desgirado com zero exatamente na meia-abscissa;
- cotas quantitativas do tilt;
- bulk Green como momento, readout log-jet e traço vertical;
- separação entre massa e amplitude;
- equivalência entre uniformidade de atlas e testes Bessel;
- estimativa ponderada com perda exata $p$;
- no-go para uma prova vertical abstrata;
- eixo centrado de carry com norma $(p-1)/p$;
- Bessel aritmética não ponderada;
- crosswalk exato dos readouts Green para o estado comum de defeitos centrados;
- ledger de norma com constantes universais $1$ e $2$.

### 23.2. Não declarado

- nenhuma instância de `GenuineKernelIncludedInGreenLimitKernel`;
- nenhuma instância de `GenuineZeroProvidesPrimeHalfAmplitudeSmoothing`;
- nenhuma cota uniforme dos estados $X_{M,s,S}$ derivada de `G(s)=0`;
- nenhuma identificação de fechamento horizontal com fechamento Green;
- nenhum teorema final de não-anulação forte fora da linha;
- nenhum uso de resultados numéricos como prova.

## 24. Mapa dos módulos desta continuação

| Camada | Módulo principal | Conteúdo |
|---|---|---|
| Guardas globais | `CpGenuineGreenKernelInclusion` | equivalências da ponte final |
| Carrier local | `CpTateCarryLocalCarrier` | torre $p^{-ks}$, dressing e mismatch |
| Guarda radial | `CpCriticalRadialBracketGuard` | fechamento radial ↔ teorema forte |
| C2 abstrato | `CpConnectedC2Defect` | cumulante e Richardson |
| Porta C2 | `CpConnectedC2TfvdPort` | cumulante como wedge TFVD |
| Pushforward | `Carry/C2OddCorePushforward` | correção dyádica exata |
| C2 concreto | `CpC2OddCorePushforwardTfvd` | cumulante e inversão logarítmica |
| Lift log-jet | `CpC2LogJetGpreLift` | prefixo preservado em TFVD–`G_pre` |
| Guarda `G_pre` | `CpNativeGpreConnectedC2Guard` | multiplicatividade e obstrução linear |
| One-jet TFVD | `CpC2DirichletJetTfvd` | injeção de $s$ e Leibniz |
| One-jet `G_pre` | `CpC2DirichletJetGpre` | leitura tagueada e normalização |
| Síntese cofinal | `CpC2GpreCofinalSynthesis` | reindexação full-support |
| Síntese tagueada | `CpC2GpreCofinalTaggedSynthesis` | atlas crescente e erro zero |
| Guarda Green | `CpC2GpreGreenActivationGuard` | rank-one versus energia |
| Zeta | `CpGenuineRiemannZetaIdentification` | $G=\zeta$ e reflexão |
| Tilt | família `CpGenuineTilt*` | rigidez e cotas quantitativas |
| Momento primo | `CpGenuineGprePrimeMomentCrosswalk` | bulk como momento universal |
| Readout Green | `CpGenuineGpreLogJetGreenBulkReadout` | comutador log-jet → bulk |
| Massa/amplitude | `CpGenuineGprePrimeAmplitudeUpgrade` | estado de massa e domínio |
| Grafo/traço | `CpGenuineGprePrimeAmplitudeGraph`, `CpGenuineGprePrimeVerticalTraceGate` | upgrade Hilbert e TFVD |
| Atlas/testes | `CpGenuineGprePrimeVerticalTraceAtlas`, `CpGenuineGprePrimeVerticalTraceDualTest` | uniformidade vetorial e dual |
| Bessel ponderada | `CpGenuineGprePrimeVerticalTraceWeightedBessel` | perda exata de meia amplitude |
| No-go vertical | `CpGenuineGprePrimeVerticalTraceNoGo` | estado+bracket sem traço global |
| Defeito centrado | `CpPrimeCarryDefectBessel` | Bessel aritmética não ponderada |
| Crosswalk atual | `CpPrimeCarryDefectReadoutCrosswalk` | readout Green como coeficiente dos eixos |

## 25. Assinatura matemática do checkpoint

As novas identidades centrais podem ser condensadas em:

$$
\boxed{2a_{8M}(m)-a_{4M}(m)=1}
$$

$$
\boxed{
2K_{8M}(p,q)-K_{4M}(p,q)
=
\frac12\varepsilon_{M,p}\varepsilon_{M,q}
}
$$

$$
\boxed{b_T(pq)=\log(pq)K_T(p,q)}
$$

$$
\boxed{
W_{\log}(T;p,q,s)
=K_T(p,q)\log(pq)(pq)^{-s}
}
$$

$$
\boxed{
\operatorname{NormalizedLocalReadout}_M(p,q,s)
=\log(pq)(pq)^{-s}
}
$$

$$
\boxed{
\operatorname{TaggedSyn}_L(p,q,s)
=\operatorname{CameraGap}_L(p,q,s)
}
$$

$$
\boxed{
\operatorname{genuineContinuation}(s)=\zeta(s)
\quad(0<\operatorname{Re}(s)<1)
}
$$

$$
\boxed{
\operatorname{UnwoundTiltTrace}_M(s)=0
\iff
\operatorname{Re}(s)=\frac12
}
$$

$$
\boxed{
\operatorname{LogJetReadout}_{p,M}(s)
=
\operatorname{GreenBulk}_{p,3M}(s)
}
$$

$$
\boxed{
\|\psi_p\|^2=\frac{p-1}{p},
\qquad
\left\|\sum_{p\in S}c_p\psi_p\right\|^2
\le\sum_{p\in S}c_p^2
}
$$

$$
\boxed{
\langle\psi_p,X_{M,s,S}\rangle
=
\operatorname{GreenBulk}_{p,3M}(s)
}
$$

$$
\boxed{
\sum_{p\in S}|R_p|^2
\le\|X_{M,s,S}\|^2
\le2\sum_{p\in S}|R_p|^2.
}
$$

## 26. Validação e metodologia

No checkpoint matemático `0aa69d55f8425d1f628db6f69ff0812bc583e3b4`:

- `Lean kernel audit` #531: **success**;
- auditoria estática: **success**;
- `lake build --wfail`: **success**;
- log de falha: não produzido;
- nenhum `axiom`, `sorry` ou `admit` local na superfície `CPFormal`;
- todos os imports locais do agregador resolvidos.

O script `scripts/static_audit.sh` rejeita explicitamente:

```text
axiom
sorry
admit
```

A ausência de axiomas locais não significa ausência dos axiomas fundacionais normais usados por Lean/Mathlib. O registro afirma somente que nenhum axioma específico da teoria foi introduzido para fechar as pontes documentadas.

## 27. Conclusão

As notas anteriores mostravam que a meia-abscissa é o único locus em que o canal Green do carry pode fechar e que o operador completado permanece não nulo fora desse equilíbrio.

A continuação formalizada acrescenta quatro resultados conceituais decisivos:

1. o Genuine canônico é literalmente a zeta de Riemann no strip;
2. o tilt transversal é rígido quando a fase é removida antes da compressão;
3. o bulk Green possui realizações exatas como momento Hilbert, readout log-jet e traço vertical;
4. os readouts Green são coeficientes de uma família Bessel aritmética construída a partir dos defeitos centrados de carry.

A energia Green já está colocada de modo finito, tagueado, ortogonal e quantitativamente controlado. A única obrigação remanescente é provar que um zero Genuine fornece uma cota uniforme para o estado comum de proveniência quando o atlas de câmeras primas cresce.

Em forma compacta:

$$
\boxed{
G(s)=0
\stackrel{\text{a provar}}{\Longrightarrow}
\sup_S\|X_{1,s,S}\|<\infty
\Longrightarrow
\sum_p|\operatorname{GreenBulk}_p(s)|^2<\infty
\Longrightarrow
\operatorname{Re}(s)=\frac12.
}
$$

Todo o mecanismo depois da primeira seta está formalizado e kernel-checked.
