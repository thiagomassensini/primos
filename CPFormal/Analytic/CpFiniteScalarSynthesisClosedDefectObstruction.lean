import CPFormal.Analytic.CpFiniteScalarSynthesisSummationByParts

/-!
# Obstrucao assintotica do defeito fechado da sintese escalar

O defeito fechado do checkpoint 0.43 nao e um erro pequeno separado do
pareamento Green. O ledger finito ja o determina exatamente como

`ClosedBulkDefect_M = ScalarPairing_M - M * GreenPairing_(3M)`.

Neste modulo orientamos essa igualdade para abrir o defeito e provamos uma
consequencia que nao usa zero Genuine: em todo o strip critico, sua parte
real tende a menos infinito. De fato, o observavel escalar converge, enquanto
a parte real do Green permanece uniformemente positiva e e multiplicada por
`M`.

Assim o defeito e um contratermo linear da compressao escalar, nao uma
correcao assintoticamente pequena. Nenhuma hipotese de zero, equacao
funcional, Zeta ou conclusao sobre a linha critica entra na prova.
-/

open scoped BigOperators Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-! ## Abertura local antes da compressao escalar -/

/-- Cada bloco angular e o bracket Genuine canonico mais um cobordo de
vertices externos. Esta identidade mantem separadas a segunda diferenca
local e a informacao de bordo que a sintese escalar comprime. -/
theorem canonicalAngularGradientBlock_eq_bracket_add_coboundary
    (m : ℕ) (s : ℂ) :
    canonicalAngularGradientBlock m s =
      realCpSaturatedBracket 3 m s +
        positiveDirichletValue s (3 * m) -
        positiveDirichletValue s (3 * (m + 1)) := by
  rw [canonicalAngularGradientBlock_eq_values,
    realCpSaturatedBracket_three_eq_values,
    positiveDirichletValue_eq_natDirichletTerm,
    positiveDirichletValue_eq_natDirichletTerm]
  have h : 3 * (m + 1) + 1 = 3 * m + 4 := by omega
  rw [h]
  ring

/-! ## Reclassificacao do defeito fechado -/

/-- O defeito fechado orientado como observavel escalar menos crescimento
Green. Esta e apenas a forma resolvida do ledger finito do checkpoint 0.43. -/
theorem finiteCanonicalAngularClosedBulkDefect_eq_scalar_sub_mul_green
    (M : ℕ) (s : ℂ) :
    finiteCanonicalAngularClosedBulkDefect M s =
      finiteCanonicalAngularScalarPairing M s -
        (M : ℂ) * finiteReflectedGradientPairing (3 * M) s := by
  have hledger :=
    finiteCanonicalAngularScalarPairing_eq_mul_green_add_closedBulkDefect M s
  rw [hledger]
  ring

/-- No strip, o observavel escalar converge para o produto das duas cartas
angulares limite. Nao se exige que nenhuma das duas cartas se anule. -/
theorem finiteCanonicalAngularScalarPairing_tendsto
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ ↦ finiteCanonicalAngularScalarPairing M s)
      atTop
      (nhds
        ((starRingEnd ℂ) (bracketedDirichletChart 3 s) *
          bracketedDirichletChart 3 (reflectedParameter s))) := by
  have htrace :
      Tendsto
        (fun M : ℕ ↦ finiteCanonicalAngularTrace M s)
        atTop (nhds (bracketedDirichletChart 3 s)) :=
    finiteCanonicalAngularTrace_tendsto hs.1
  have htraceSharp :
      Tendsto
        (fun M : ℕ ↦
          finiteCanonicalAngularTrace M (reflectedParameter s))
        atTop
        (nhds (bracketedDirichletChart 3 (reflectedParameter s))) :=
    finiteCanonicalAngularTrace_reflected_tendsto hs
  have htraceConj :
      Tendsto
        (fun M : ℕ ↦
          (starRingEnd ℂ) (finiteCanonicalAngularTrace M s))
        atTop
        (nhds ((starRingEnd ℂ) (bracketedDirichletChart 3 s))) := by
    simpa [Function.comp_def] using
      (Complex.continuous_conj.tendsto
        (bracketedDirichletChart 3 s)).comp htrace
  have hproduct := htraceConj.mul htraceSharp
  simpa only [finiteCanonicalAngularScalarPairing_eq_product] using hproduct

/--
A parte real do defeito fechado diverge para menos infinito em todo ponto do
strip. O resultado e independente de zeros Genuine: o pareamento escalar
possui limite finito, enquanto `M * Re(Green_(3M))` cresce ao menos
linearmente a partir da primeira aresta positiva.
-/
theorem finiteCanonicalAngularClosedBulkDefect_re_tendsto_atBot
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ ↦
        (finiteCanonicalAngularClosedBulkDefect M s).re)
      atTop atBot := by
  let c : ℝ := (finiteReflectedGradientPairing 1 s).re
  have hc : 0 < c := by
    exact finiteReflectedGradientPairing_re_pos (by norm_num) hs
  have hgreenMonotone := finiteReflectedGradientPairing_re_monotone hs
  have hlinear :
      Tendsto (fun M : ℕ ↦ (M : ℝ) * c) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hc
  have hgreenGrowth :
      Tendsto
        (fun M : ℕ ↦
          (M : ℝ) * (finiteReflectedGradientPairing (3 * M) s).re)
        atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hlinear
    filter_upwards [eventually_ge_atTop 1] with M hM
    have hpairing :
        (finiteReflectedGradientPairing 1 s).re ≤
          (finiteReflectedGradientPairing (3 * M) s).re :=
      hgreenMonotone (by omega)
    exact mul_le_mul_of_nonneg_left
      (by simpa only [c] using hpairing)
      (by positivity)
  have hnegativeGrowth :
      Tendsto
        (fun M : ℕ ↦
          -((M : ℝ) *
            (finiteReflectedGradientPairing (3 * M) s).re))
        atTop atBot :=
    tendsto_neg_atBot_iff.mpr hgreenGrowth
  have hscalar := finiteCanonicalAngularScalarPairing_tendsto hs
  have hscalarRe :
      Tendsto
        (fun M : ℕ ↦ (finiteCanonicalAngularScalarPairing M s).re)
        atTop
        (nhds
          (((starRingEnd ℂ) (bracketedDirichletChart 3 s) *
            bracketedDirichletChart 3 (reflectedParameter s)).re)) := by
    simpa [Function.comp_def] using
      Complex.continuous_re.continuousAt.tendsto.comp hscalar
  have hsum :
      Tendsto
        (fun M : ℕ ↦
          -((M : ℝ) *
              (finiteReflectedGradientPairing (3 * M) s).re) +
            (finiteCanonicalAngularScalarPairing M s).re)
        atTop atBot :=
    Tendsto.atBot_add hnegativeGrowth hscalarRe
  have hpoint (M : ℕ) :
      (finiteCanonicalAngularClosedBulkDefect M s).re =
        -((M : ℝ) *
            (finiteReflectedGradientPairing (3 * M) s).re) +
          (finiteCanonicalAngularScalarPairing M s).re := by
    rw [finiteCanonicalAngularClosedBulkDefect_eq_scalar_sub_mul_green]
    simp only [Complex.sub_re, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, zero_mul, sub_zero]
    ring
  simpa only [hpoint] using hsum

/-!
## Guardrail normalizado

A divergencia linear acima nao e um artefato da escala absoluta. Depois de
dividir o corte `M+1` por seu tamanho, o termo escalar desaparece, enquanto
o Green conserva pelo menos metade da margem positiva da primeira aresta.
Logo o defeito normalizado permanece estritamente no semiplano real negativo
e, em particular, nao pode convergir a zero.
-/

/-- Eventualmente a parte real do defeito normalizado fica abaixo de menos
metade da primeira energia Green. -/
theorem eventually_normalizedClosedBulkDefect_re_lt_neg_half
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    ∀ᶠ M : ℕ in atTop,
      ((((M + 1 : ℕ) : ℂ))⁻¹ *
          finiteCanonicalAngularClosedBulkDefect (M + 1) s).re <
        -((finiteReflectedGradientPairing 1 s).re / 2) := by
  let scalarLimit : ℂ :=
    (starRingEnd ℂ) (bracketedDirichletChart 3 s) *
      bracketedDirichletChart 3 (reflectedParameter s)
  have hscalar :
      Tendsto
        (fun M : ℕ ↦ finiteCanonicalAngularScalarPairing M s)
        atTop (nhds scalarLimit) := by
    simpa only [scalarLimit] using
      finiteCanonicalAngularScalarPairing_tendsto hs
  have hscalarShift :
      Tendsto
        (fun M : ℕ ↦ finiteCanonicalAngularScalarPairing (M + 1) s)
        atTop (nhds scalarLimit) :=
    hscalar.comp (tendsto_add_atTop_nat 1)
  have hinv :
      Tendsto (fun M : ℕ ↦ (((M + 1 : ℕ) : ℂ))⁻¹)
        atTop (nhds 0) :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)).comp
      (tendsto_add_atTop_nat 1)
  have hscaledScalarComplex :
      Tendsto
        (fun M : ℕ ↦
          (((M + 1 : ℕ) : ℂ))⁻¹ *
            finiteCanonicalAngularScalarPairing (M + 1) s)
        atTop (nhds 0) := by
    simpa only [zero_mul] using hinv.mul hscalarShift
  have hscaledScalarReal :
      Tendsto
        (fun M : ℕ ↦
          ((((M + 1 : ℕ) : ℂ))⁻¹ *
            finiteCanonicalAngularScalarPairing (M + 1) s).re)
        atTop (nhds 0) := by
    simpa [Function.comp_def] using
      Complex.continuous_re.continuousAt.tendsto.comp hscaledScalarComplex
  have hc : 0 < (finiteReflectedGradientPairing 1 s).re :=
    finiteReflectedGradientPairing_re_pos (by norm_num) hs
  have hscalarSmall :
      ∀ᶠ M : ℕ in atTop,
        ((((M + 1 : ℕ) : ℂ))⁻¹ *
          finiteCanonicalAngularScalarPairing (M + 1) s).re <
            (finiteReflectedGradientPairing 1 s).re / 2 :=
    hscaledScalarReal.eventually (Iio_mem_nhds (half_pos hc))
  have hgreenMonotone := finiteReflectedGradientPairing_re_monotone hs
  filter_upwards [hscalarSmall] with M hsmall
  let N : ℕ := M + 1
  have hN : (N : ℂ) ≠ 0 := by
    exact_mod_cast (show N ≠ 0 by omega)
  have hnormalized :
      (N : ℂ)⁻¹ * finiteCanonicalAngularClosedBulkDefect N s =
        (N : ℂ)⁻¹ * finiteCanonicalAngularScalarPairing N s -
          finiteReflectedGradientPairing (3 * N) s := by
    rw [finiteCanonicalAngularClosedBulkDefect_eq_scalar_sub_mul_green]
    field_simp [hN]
  have hgreenLower :
      (finiteReflectedGradientPairing 1 s).re ≤
        (finiteReflectedGradientPairing (3 * N) s).re :=
    hgreenMonotone (by omega)
  change
    (((N : ℂ)⁻¹ * finiteCanonicalAngularClosedBulkDefect N s).re <
      -((finiteReflectedGradientPairing 1 s).re / 2))
  rw [hnormalized, Complex.sub_re]
  linarith

/-- Guardrail linear: o defeito fechado dividido pelo tamanho do corte nao
converge a zero em nenhum ponto do strip critico. -/
theorem normalizedClosedBulkDefect_not_tendsto_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    ¬ Tendsto
      (fun M : ℕ ↦
        (((M + 1 : ℕ) : ℂ))⁻¹ *
          finiteCanonicalAngularClosedBulkDefect (M + 1) s)
      atTop (nhds 0) := by
  intro hzero
  have hreal :
      Tendsto
        (fun M : ℕ ↦
          ((((M + 1 : ℕ) : ℂ))⁻¹ *
            finiteCanonicalAngularClosedBulkDefect (M + 1) s).re)
        atTop (nhds 0) := by
    simpa [Function.comp_def] using
      Complex.continuous_re.continuousAt.tendsto.comp hzero
  have hnegative :=
    eventually_normalizedClosedBulkDefect_re_lt_neg_half hs
  have hlimitUpper :
      (0 : ℝ) ≤ -((finiteReflectedGradientPairing 1 s).re / 2) :=
    le_of_tendsto hreal (hnegative.mono fun _ h ↦ le_of_lt h)
  have hc : 0 < (finiteReflectedGradientPairing 1 s).re :=
    finiteReflectedGradientPairing_re_pos (by norm_num) hs
  linarith

end

end CPFormal.Analytic.Cp
