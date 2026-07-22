import CPFormal.Analytic.CpFiniteSeededTfvdGreenIdentity
import CPFormal.Analytic.CpGenuineGreenCompletedOperator

/-!
# Observabilidade Genuine pela concordancia de proveniencia entre cameras

A forma de bordo `same-s` da TFVD e independente da camera prima. Para cada
camera, a identidade finita a decompõe como

`BoundaryForm = Green_p + Provenance_p`.

Comparar duas cameras elimina a forma de bordo comum e deixa uma identidade
exata entre a diferenca de proveniencias e a diferenca dos fluxos Green. A
positividade do pareamento refletido mostra entao que, em qualquer cutoff nao
vazio, as partes reais das proveniencias de duas cameras primas distintas
coincidem se, e somente se, o deslocamento critico e zero.

Este modulo nao presume que um zero Genuine sincroniza as proveniencias. Ele
isola essa sincronizacao como a forma cross-prime mais fraca da obrigacao de
observabilidade: basta concordancia entre as cameras, sem exigir que cada
fluxo Green se anule separadamente.
-/

open scoped Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-! ## Identidade finita de diferenca de proveniencias -/

/-- Eliminar a forma TFVD comum deixa exatamente a diferenca oposta dos
fluxos Green Genuine das duas cameras. -/
theorem finiteCanonicalTfvdSameSGreenProvenanceDefect_sub_eq_greenFlux_sub
    (p q M : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (s : ℂ) :
    finiteCanonicalTfvdSameSGreenProvenanceDefect p M s -
        finiteCanonicalTfvdSameSGreenProvenanceDefect q M s =
      finiteOrientedGenuineCpGreenFlux q (3 * M) s -
        finiteOrientedGenuineCpGreenFlux p (3 * M) s := by
  have hpIdentity :=
    finiteCanonicalSeededTfvdSameSBoundaryForm_eq_green_add_provenance
      p hp M (kappa := (1 : ℂ)) (by norm_num)
      (fun _ : ℕ => (1 : ℂ)) (by intro m; norm_num) s
  have hqIdentity :=
    finiteCanonicalSeededTfvdSameSBoundaryForm_eq_green_add_provenance
      q hq M (kappa := (1 : ℂ)) (by norm_num)
      (fun _ : ℕ => (1 : ℂ)) (by intro m; norm_num) s
  linear_combination hqIdentity - hpIdentity

/-- Forma radial resolvida da diferenca: a proveniencia mede a diferenca dos
coeficientes radiais aplicada ao mesmo pareamento refletido. -/
theorem finiteCanonicalTfvdSameSGreenProvenanceDefect_sub_eq_radialDifference_mul
    (p q M : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (s : ℂ) :
    finiteCanonicalTfvdSameSGreenProvenanceDefect p M s -
        finiteCanonicalTfvdSameSGreenProvenanceDefect q M s =
      ((cpRadialDifference q (criticalDisplacement s.re) -
          cpRadialDifference p (criticalDisplacement s.re) : ℝ) : ℂ) *
        finiteReflectedGradientPairing (3 * M) s := by
  rw [finiteCanonicalTfvdSameSGreenProvenanceDefect_sub_eq_greenFlux_sub
      p q M hp hq s,
    finiteOrientedGenuineCpGreenFlux_eq_finiteOrientedCpGreenFlux
      q (3 * M) hq s,
    finiteOrientedGenuineCpGreenFlux_eq_finiteOrientedCpGreenFlux
      p (3 * M) hp s,
    finiteOrientedCpGreenFlux_eq_radialDifference_mul_pairing
      q (3 * M) hq s,
    finiteOrientedCpGreenFlux_eq_radialDifference_mul_pairing
      p (3 * M) hp s]
  push_cast
  ring

/-! ## Rigidez finita da concordancia de proveniencia -/

/-- Em duas cameras primas distintas e num cutoff nao vazio, a concordancia
das partes reais da proveniencia detecta exatamente o equilibrio transversal. -/
theorem finiteCanonicalTfvdSameSGreenProvenanceDefect_re_eq_iff
    (p q M : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (hM : 0 < M)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    (finiteCanonicalTfvdSameSGreenProvenanceDefect p M s).re =
        (finiteCanonicalTfvdSameSGreenProvenanceDefect q M s).re ↔
      criticalDisplacement s.re = 0 := by
  let delta := criticalDisplacement s.re
  constructor
  · intro hprovenance
    have hsubRe :
        (finiteCanonicalTfvdSameSGreenProvenanceDefect p M s -
          finiteCanonicalTfvdSameSGreenProvenanceDefect q M s).re = 0 := by
      simp only [Complex.sub_re]
      linarith
    rw [finiteCanonicalTfvdSameSGreenProvenanceDefect_sub_eq_radialDifference_mul
      p q M hp hq s] at hsubRe
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at hsubRe
    have henergy :
        0 < (finiteReflectedGradientPairing (3 * M) s).re :=
      finiteReflectedGradientPairing_re_pos (by omega) hs
    have hcoeff :
        cpRadialDifference q delta - cpRadialDifference p delta = 0 :=
      (mul_eq_zero.mp hsubRe).resolve_right (ne_of_gt henergy)
    have heq :
        cpRadialDifference p delta = cpRadialDifference q delta := by
      linarith
    exact (cpRadialDifference_eq_cpRadialDifference_iff
      p q hp hq hpq delta).1 heq
  · intro hcritical
    have heq := (cpRadialDifference_eq_cpRadialDifference_iff
      p q hp hq hpq delta).2 hcritical
    have hsub :
        finiteCanonicalTfvdSameSGreenProvenanceDefect p M s -
            finiteCanonicalTfvdSameSGreenProvenanceDefect q M s = 0 := by
      rw [finiteCanonicalTfvdSameSGreenProvenanceDefect_sub_eq_radialDifference_mul
        p q M hp hq s]
      simp [delta, heq]
    exact congrArg Complex.re (sub_eq_zero.mp hsub)

/-! ## Limite e criterio assintotico -/

/-- A diferenca real das proveniencias converge para a diferenca dos dois
coeficientes radiais multiplicada pela energia Green infinita positiva. -/
theorem finiteCanonicalTfvdSameSGreenProvenanceDefect_re_sub_tendsto
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ =>
        (finiteCanonicalTfvdSameSGreenProvenanceDefect p M s -
          finiteCanonicalTfvdSameSGreenProvenanceDefect q M s).re)
      atTop
      (nhds
        ((cpRadialDifference q (criticalDisplacement s.re) -
            cpRadialDifference p (criticalDisplacement s.re)) *
          infiniteReflectedGreenEnergy s)) := by
  have hthree : Tendsto (fun M : ℕ => 3 * M) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with M hM
    omega
  have henergy :=
    (finiteReflectedGradientPairing_re_tendsto_infiniteEnergy hs).comp hthree
  have hscaled :=
    (tendsto_const_nhds :
      Tendsto
        (fun _ : ℕ =>
          cpRadialDifference q (criticalDisplacement s.re) -
            cpRadialDifference p (criticalDisplacement s.re))
        atTop
        (nhds
          (cpRadialDifference q (criticalDisplacement s.re) -
            cpRadialDifference p (criticalDisplacement s.re)))).mul henergy
  have hfunctions :
      (fun M : ℕ =>
        (finiteCanonicalTfvdSameSGreenProvenanceDefect p M s -
          finiteCanonicalTfvdSameSGreenProvenanceDefect q M s).re) =
      (fun M : ℕ =>
        (cpRadialDifference q (criticalDisplacement s.re) -
            cpRadialDifference p (criticalDisplacement s.re)) *
          (finiteReflectedGradientPairing (3 * M) s).re) := by
    funext M
    rw [finiteCanonicalTfvdSameSGreenProvenanceDefect_sub_eq_radialDifference_mul
      p q M hp hq s]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  rw [hfunctions]
  exact hscaled

/-- Assintoticamente, sincronizar as duas proveniencias e equivalente a
anular o deslocamento critico. -/
theorem finiteCanonicalTfvdSameSGreenProvenanceDefect_re_sub_tendsto_zero_iff
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Tendsto
        (fun M : ℕ =>
          (finiteCanonicalTfvdSameSGreenProvenanceDefect p M s -
            finiteCanonicalTfvdSameSGreenProvenanceDefect q M s).re)
        atTop (nhds 0) ↔
      criticalDisplacement s.re = 0 := by
  let delta := criticalDisplacement s.re
  let E := infiniteReflectedGreenEnergy s
  have hlimit :=
    finiteCanonicalTfvdSameSGreenProvenanceDefect_re_sub_tendsto
      p q hp hq hs
  constructor
  · intro hzero
    have hproduct :
        (cpRadialDifference q delta - cpRadialDifference p delta) * E = 0 := by
      simpa [delta, E] using tendsto_nhds_unique hlimit hzero
    have hE : E ≠ 0 := ne_of_gt (infiniteReflectedGreenEnergy_pos hs)
    have hcoeff :
        cpRadialDifference q delta - cpRadialDifference p delta = 0 :=
      (mul_eq_zero.mp hproduct).resolve_right hE
    have heq :
        cpRadialDifference p delta = cpRadialDifference q delta := by
      linarith
    exact (cpRadialDifference_eq_cpRadialDifference_iff
      p q hp hq hpq delta).1 heq
  · intro hcritical
    have heq := (cpRadialDifference_eq_cpRadialDifference_iff
      p q hp hq hpq delta).2 hcritical
    simpa [delta, E, heq] using hlimit

end

end CPFormal.Analytic.Cp
