import CPFormal.Analytic.CpGenuineGreenCompletedOperator
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Perfil Green multiprima na amplitude critica do carry

Cada camera prima possui no limite Green o coeficiente radial

`cpRadialDifference p delta`.

Vestir esse coeficiente pela amplitude critica da primeira camada do carry,
`primeCarryAmplitudeRatio p = p^(-1/2)`, produz um perfil sobre todas as
cameras primas. Este modulo prova o limiar quadratico exato: o perfil e
quadrado-somavel se, e somente se, `delta = 0`.

A direcao off-critical usa apenas que a soma de `1 / p` sobre os primos
diverge. Ela nao presume que um zero Genuine produza um vetor multiprima de
energia finita; essa propriedade de Bessel permanece uma obrigacao separada
de observabilidade do operador aritmetico.
-/

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-- O quadrado da amplitude critica da primeira camada e a massa `1 / p`. -/
theorem primeCarryAmplitudeRatio_sq_eq_inv (p : ℕ) :
    (primeCarryAmplitudeRatio p) ^ 2 = (p : ℝ)⁻¹ := by
  have hpnonneg : (0 : ℝ) ≤ (p : ℝ) := by positivity
  unfold primeCarryAmplitudeRatio
  rw [inv_pow, Real.sq_sqrt hpnonneg]

/-- Trocar o sinal do deslocamento troca apenas a orientacao da diferenca
radial. -/
@[simp] theorem cpRadialDifference_neg (p : ℕ) (delta : ℝ) :
    cpRadialDifference p (-delta) = -cpRadialDifference p delta := by
  unfold cpRadialDifference
  simp only [neg_neg]
  ring

/-- Fora do equilibrio, a magnitude da diferenca radial da camera `2` e um
lower bound uniforme para todas as cameras primas. -/
theorem abs_cpRadialDifference_two_le_prime
    (delta : ℝ) (hdelta : delta ≠ 0) (p : Nat.Primes) :
    |cpRadialDifference 2 delta| ≤
      |cpRadialDifference p delta| := by
  have hpTwoNat : 2 ≤ (p : ℕ) := p.prop.two_le
  have hpTwo : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpTwoNat
  rcases lt_or_gt_of_ne hdelta with hdeltaNeg | hdeltaPos
  · have hpositive : 0 < -delta := neg_pos.mpr hdeltaNeg
    have hpowPos :
        (2 : ℝ) ^ (-delta) ≤ (p : ℝ) ^ (-delta) :=
      Real.rpow_le_rpow (by norm_num) hpTwo hpositive.le
    have hpowNeg :
        (p : ℝ) ^ delta ≤ (2 : ℝ) ^ delta :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hpTwo hdeltaNeg.le
    have htwoNonpos : cpRadialDifference 2 delta ≤ 0 := by
      rw [cpRadialDifference_eq_two_mul_delta_mul_cofactor]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith)
        (le_of_lt (cpRadialCofactor_pos 2 (by norm_num) delta))
    have hpNonpos : cpRadialDifference p delta ≤ 0 := by
      rw [cpRadialDifference_eq_two_mul_delta_mul_cofactor]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith)
        (le_of_lt (cpRadialCofactor_pos p p.prop delta))
    rw [abs_of_nonpos htwoNonpos, abs_of_nonpos hpNonpos]
    calc
      -cpRadialDifference 2 delta =
          (2 : ℝ) ^ (-delta) - (2 : ℝ) ^ delta := by
            unfold cpRadialDifference
            ring_nf
      _ ≤ (p : ℝ) ^ (-delta) - (2 : ℝ) ^ delta :=
        sub_le_sub_right hpowPos _
      _ ≤ (p : ℝ) ^ (-delta) - (p : ℝ) ^ delta :=
        sub_le_sub_left hpowNeg _
      _ = -cpRadialDifference p delta := by
        unfold cpRadialDifference
        ring_nf
  · have hpowPos :
        (2 : ℝ) ^ delta ≤ (p : ℝ) ^ delta :=
      Real.rpow_le_rpow (by norm_num) hpTwo hdeltaPos.le
    have hpowNeg :
        (p : ℝ) ^ (-delta) ≤ (2 : ℝ) ^ (-delta) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hpTwo (by linarith)
    have htwoNonneg : 0 ≤ cpRadialDifference 2 delta := by
      rw [cpRadialDifference_eq_two_mul_delta_mul_cofactor]
      exact mul_nonneg (by positivity)
        (le_of_lt (cpRadialCofactor_pos 2 (by norm_num) delta))
    have hpNonneg : 0 ≤ cpRadialDifference p delta := by
      rw [cpRadialDifference_eq_two_mul_delta_mul_cofactor]
      exact mul_nonneg (by positivity)
        (le_of_lt (cpRadialCofactor_pos p p.prop delta))
    rw [abs_of_nonneg htwoNonneg, abs_of_nonneg hpNonneg]
    calc
      cpRadialDifference 2 delta =
          (2 : ℝ) ^ delta - (2 : ℝ) ^ (-delta) := rfl
      _ ≤ (p : ℝ) ^ delta - (2 : ℝ) ^ (-delta) :=
        sub_le_sub_right hpowPos _
      _ ≤ (p : ℝ) ^ delta - (p : ℝ) ^ (-delta) :=
        sub_le_sub_left hpowNeg _
      _ = cpRadialDifference p delta := rfl

/-- Perfil radial de todas as cameras, vestido pela amplitude critica do
carry. -/
def primeCarryGreenRadialProfile
    (delta : ℝ) (p : Nat.Primes) : ℝ :=
  primeCarryAmplitudeRatio p * cpRadialDifference p delta

/-- Comparacao ponto a ponto com uma constante positiva vezes `1 / p`. -/
theorem primeCarryGreenRadialProfile_lower_bound
    (delta : ℝ) (hdelta : delta ≠ 0) (p : Nat.Primes) :
    |cpRadialDifference 2 delta| ^ 2 * (1 / (p : ℝ)) ≤
      (primeCarryGreenRadialProfile delta p) ^ 2 := by
  have hradialSq :
      (cpRadialDifference 2 delta) ^ 2 ≤
        (cpRadialDifference p delta) ^ 2 :=
    sq_le_sq.mpr (abs_cpRadialDifference_two_le_prime delta hdelta p)
  rw [primeCarryGreenRadialProfile, mul_pow,
    primeCarryAmplitudeRatio_sq_eq_inv]
  rw [← one_div]
  have hpNonneg : 0 ≤ (1 / (p : ℝ)) := by positivity
  calc
    |cpRadialDifference 2 delta| ^ 2 * (1 / (p : ℝ)) =
        (1 / (p : ℝ)) * (cpRadialDifference 2 delta) ^ 2 := by
      rw [sq_abs]
      ring
    _ ≤ (1 / (p : ℝ)) * (cpRadialDifference p delta) ^ 2 :=
      mul_le_mul_of_nonneg_left hradialSq hpNonneg
    _ = (1 / (p : ℝ)) * (cpRadialDifference p delta) ^ 2 := rfl

/-- Fora do equilibrio, o perfil radial vestido nao e quadrado-somavel sobre
as cameras primas. -/
theorem not_summable_primeCarryGreenRadialProfile_sq
    (delta : ℝ) (hdelta : delta ≠ 0) :
    ¬ Summable (fun p : Nat.Primes =>
      (primeCarryGreenRadialProfile delta p) ^ 2) := by
  intro hprofile
  let c : ℝ := |cpRadialDifference 2 delta| ^ 2
  have hradialTwo : cpRadialDifference 2 delta ≠ 0 :=
    (cpRadialDifference_eq_zero_iff 2 (by norm_num) delta).not.mpr hdelta
  have hc : c ≠ 0 := by
    dsimp [c]
    exact pow_ne_zero 2 (abs_ne_zero.mpr hradialTwo)
  have hscaled : Summable (fun p : Nat.Primes => c * (1 / (p : ℝ))) :=
    hprofile.of_nonneg_of_le
      (fun p => mul_nonneg (sq_nonneg _) (by positivity))
      (fun p => by
        dsimp [c]
        exact primeCarryGreenRadialProfile_lower_bound delta hdelta p)
  have honeDiv : Summable (fun p : Nat.Primes => (1 / (p : ℝ))) := by
    have hinv := hscaled.mul_left c⁻¹
    simpa [mul_assoc, hc] using hinv
  exact Nat.Primes.not_summable_one_div honeDiv

/-- Perfil Green limite completo, incluindo a energia refletida comum a
todas as cameras. -/
def primeCarryGreenLimitProfile
    (s : ℂ) (p : Nat.Primes) : ℝ :=
  primeCarryGreenRadialProfile (criticalDisplacement s.re) p *
    infiniteReflectedGreenEnergy s

/-- A energia Green positiva nao altera o limiar de quadrado-somabilidade do
perfil multiprima. -/
theorem summable_primeCarryGreenLimitProfile_sq_iff
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Summable (fun p : Nat.Primes =>
        (primeCarryGreenLimitProfile s p) ^ 2) ↔
      criticalDisplacement s.re = 0 := by
  let delta := criticalDisplacement s.re
  let E := infiniteReflectedGreenEnergy s
  have hE : E ≠ 0 := ne_of_gt (infiniteReflectedGreenEnergy_pos hs)
  have hEActual : infiniteReflectedGreenEnergy s ≠ 0 := by
    simpa [E] using hE
  constructor
  · intro hsummable
    by_contra hdelta
    have hscaled := hsummable.mul_left (E ^ 2)⁻¹
    have hradial : Summable (fun p : Nat.Primes =>
        (primeCarryGreenRadialProfile delta p) ^ 2) := by
      have hfunctions :
          (fun p : Nat.Primes =>
            (E ^ 2)⁻¹ * (primeCarryGreenLimitProfile s p) ^ 2) =
          (fun p : Nat.Primes =>
            (primeCarryGreenRadialProfile delta p) ^ 2) := by
        funext p
        dsimp [primeCarryGreenLimitProfile, delta, E]
        rw [mul_pow]
        calc
          (infiniteReflectedGreenEnergy s ^ 2)⁻¹ *
                (primeCarryGreenRadialProfile
                    (criticalDisplacement s.re) p ^ 2 *
                  infiniteReflectedGreenEnergy s ^ 2) =
              primeCarryGreenRadialProfile
                  (criticalDisplacement s.re) p ^ 2 *
                ((infiniteReflectedGreenEnergy s ^ 2)⁻¹ *
                  infiniteReflectedGreenEnergy s ^ 2) := by ring
          _ = primeCarryGreenRadialProfile
                (criticalDisplacement s.re) p ^ 2 := by
            simp [hEActual]
      rw [hfunctions] at hscaled
      exact hscaled
    exact not_summable_primeCarryGreenRadialProfile_sq delta hdelta hradial
  · intro hdelta
    have hzero : ∀ p : Nat.Primes,
        primeCarryGreenLimitProfile s p = 0 := by
      intro p
      simp [primeCarryGreenLimitProfile, primeCarryGreenRadialProfile,
        hdelta, cpRadialDifference]
    simpa only [hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (summable_zero : Summable (fun _ : Nat.Primes => (0 : ℝ)))

/-! ## Perfil de bulk em cutoff finito -/

/-- Antes de somar ortogonalmente sobre os primos, o bordo comum deve ser
retirado. Caso contrario, seu quadrado seria repetido com peso `1 / p` e a
soma divergiria sempre que o bordo fosse apenas assintoticamente, mas nao
identicamente, nulo. -/
def primeCarryGreenBulkCutoffProfile
    (M : ℕ) (s : ℂ) (p : Nat.Primes) : ℝ :=
  primeCarryAmplitudeRatio p *
    (finiteBracketCoupledCpGreenFlux p M s -
      finiteBracketCoupledSignedBoundary M s)

/-- Depois de retirar o bordo comum, cada coordenada finita e literalmente o
perfil radial vestido multiplicado pela mesma energia refletida do cutoff. -/
theorem primeCarryGreenBulkCutoffProfile_eq
    (M : ℕ) (s : ℂ) (p : Nat.Primes) :
    primeCarryGreenBulkCutoffProfile M s p =
      primeCarryGreenRadialProfile (criticalDisplacement s.re) p *
        (finiteReflectedGradientPairing M s).re := by
  rw [primeCarryGreenBulkCutoffProfile,
    finiteBracketCoupledCpGreenFlux_eq_radialDifference_mul_pairing
      (p : ℕ) M p.prop s]
  unfold primeCarryGreenRadialProfile
  ring

/-- Em qualquer cutoff nao vazio, o bulk vestido e quadrado-somavel sobre
todas as cameras primas se, e somente se, o deslocamento critico e zero. -/
theorem summable_primeCarryGreenBulkCutoffProfile_sq_iff
    (M : ℕ) (hM : 0 < M)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Summable (fun p : Nat.Primes =>
        (primeCarryGreenBulkCutoffProfile M s p) ^ 2) ↔
      criticalDisplacement s.re = 0 := by
  let delta := criticalDisplacement s.re
  let E := (finiteReflectedGradientPairing M s).re
  have hE : E ≠ 0 :=
    ne_of_gt (finiteReflectedGradientPairing_re_pos hM hs)
  have hEActual : (finiteReflectedGradientPairing M s).re ≠ 0 := by
    simpa [E] using hE
  constructor
  · intro hsummable
    by_contra hdelta
    have hscaled := hsummable.mul_left (E ^ 2)⁻¹
    have hradial : Summable (fun p : Nat.Primes =>
        (primeCarryGreenRadialProfile delta p) ^ 2) := by
      have hfunctions :
          (fun p : Nat.Primes =>
            (E ^ 2)⁻¹ *
              (primeCarryGreenBulkCutoffProfile M s p) ^ 2) =
          (fun p : Nat.Primes =>
            (primeCarryGreenRadialProfile delta p) ^ 2) := by
        funext p
        rw [primeCarryGreenBulkCutoffProfile_eq, mul_pow]
        dsimp [delta, E]
        calc
          ((finiteReflectedGradientPairing M s).re ^ 2)⁻¹ *
                (primeCarryGreenRadialProfile
                    (criticalDisplacement s.re) p ^ 2 *
                  (finiteReflectedGradientPairing M s).re ^ 2) =
              primeCarryGreenRadialProfile
                  (criticalDisplacement s.re) p ^ 2 *
                (((finiteReflectedGradientPairing M s).re ^ 2)⁻¹ *
                  (finiteReflectedGradientPairing M s).re ^ 2) := by ring
          _ = primeCarryGreenRadialProfile
                (criticalDisplacement s.re) p ^ 2 := by
            simp [hEActual]
      rw [hfunctions] at hscaled
      exact hscaled
    exact not_summable_primeCarryGreenRadialProfile_sq
      delta hdelta hradial
  · intro hdelta
    have hzero : ∀ p : Nat.Primes,
        primeCarryGreenBulkCutoffProfile M s p = 0 := by
      intro p
      rw [primeCarryGreenBulkCutoffProfile_eq]
      simp [hdelta, primeCarryGreenRadialProfile, cpRadialDifference]
    simpa only [hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (summable_zero : Summable (fun _ : Nat.Primes => (0 : ℝ)))

/-! ## Ponte Bessel concreta para a observabilidade Genuine -/

/-- Um bound Bessel em um cutoff nao vazio para os bulks com o bordo comum
retirado obriga o deslocamento critico a zerar. A obrigacao aritmetica que
permanece e deduzir tal bound a partir de um zero Genuine; ela nao e presumida
por nenhuma identidade Green deste modulo. -/
theorem criticalDisplacement_eq_zero_of_primeGreen_bulk_bessel_at_cutoff
    (M : ℕ) (hM : 0 < M)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (C : ℝ)
    (hBessel : ∀ S : Finset Nat.Primes,
      ∑ p ∈ S, (primeCarryGreenBulkCutoffProfile M s p) ^ 2 ≤ C) :
    criticalDisplacement s.re = 0 := by
  have hsummable :
      Summable (fun p : Nat.Primes =>
        (primeCarryGreenBulkCutoffProfile M s p) ^ 2) :=
    summable_of_sum_le (fun _ => sq_nonneg _) hBessel
  exact
    (summable_primeCarryGreenBulkCutoffProfile_sq_iff M hM hs).1 hsummable

/-- A versao uniforme em todos os cutoffs reduz-se ao primeiro cutoff nao
vazio; nenhum limite ou troca de somas e necessario. -/
theorem criticalDisplacement_eq_zero_of_uniform_primeGreen_bulk_bessel
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (C : ℝ)
    (hBessel : ∀ M : ℕ, ∀ S : Finset Nat.Primes,
      ∑ p ∈ S, (primeCarryGreenBulkCutoffProfile M s p) ^ 2 ≤ C) :
    criticalDisplacement s.re = 0 := by
  exact criticalDisplacement_eq_zero_of_primeGreen_bulk_bessel_at_cutoff
    1 (by norm_num) hs C (hBessel 1)

/-! ## Realizacao ortogonal que produziria o bound -/

/-- Se os bulks centrados de todas as cameras forem coeficientes de um unico
estado contra uma familia ortonormal indexada pelos primos, a desigualdade de
Bessel fornece a cota finita automaticamente. Este teorema nao constroi tal
estado; ele isola a identidade de coordenadas que a analise aritmetica global
ainda deve fornecer. -/
theorem uniform_primeGreen_bulk_bessel_of_bounded_orthonormal_realization
    {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
    (cameraAxis : Nat.Primes → H)
    (horthogonal : Orthonormal ℝ cameraAxis)
    (state : ℕ → H)
    (s : ℂ)
    (hcoordinate : ∀ M : ℕ, ∀ p : Nat.Primes,
      inner ℝ (cameraAxis p) (state M) =
        primeCarryGreenBulkCutoffProfile M s p)
    (C : ℝ) (hstate : ∀ M : ℕ, ‖state M‖ ^ 2 ≤ C) :
    ∀ M : ℕ, ∀ S : Finset Nat.Primes,
      ∑ p ∈ S, (primeCarryGreenBulkCutoffProfile M s p) ^ 2 ≤ C := by
  intro M S
  calc
    (∑ p ∈ S, (primeCarryGreenBulkCutoffProfile M s p) ^ 2) =
        ∑ p ∈ S, ‖inner ℝ (cameraAxis p) (state M)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro p _hp
          rw [hcoordinate M p, Real.norm_eq_abs, sq_abs]
    _ ≤ ‖state M‖ ^ 2 := horthogonal.sum_inner_products_le (state M)
    _ ≤ C := hstate M

end

end CPFormal.Analytic.Cp
