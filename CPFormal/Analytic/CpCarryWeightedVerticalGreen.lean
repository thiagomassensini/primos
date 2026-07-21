import CPFormal.Analytic.CpNativeGpreTowerNorm
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Green vertical vestido pela amplitude de carry

Este modulo separa explicitamente a profundidade vertical de carry da posicao
horizontal dos inteiros. O parametro `r` abaixo e uma distancia entre camadas
de uma mesma fibra, nunca o indice horizontal `n` do Green discreto ordinario.

Se `q` e a razao de amplitude entre duas camadas consecutivas, o transporte do
Green causal para coordenadas de amplitude possui nucleo

`r * q^r`.

Na especializacao geometrica, `q = p^(-1/2)`, logo o nucleo e

`r * p^(-r/2)`.

O resultado principal desta primeira camada e abstrato: para qualquer familia
de shifts contrativos, a serie desses shifts ponderados converge em norma de
operador. Portanto o Green vestido define um operador linear continuo com
majorante independente do cutoff. Nenhum zero, carta escalar ou identidade
Green de bordo e usado aqui.

A colagem coordenada de bracket, traco e retorno fica deliberadamente para um
modulo posterior; pesar apenas o interior nao e declarado como uma nova
identidade de valvula.
-/

open scoped BigOperators
open Filter

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Nucleo causal do Green depois do transporte para unidades de amplitude.
O indice `r` mede a distancia vertical entre duas camadas da mesma fibra. -/
def carryWeightedVerticalGreenKernel (q : ℝ) (r : ℕ) : ℝ :=
  (r : ℝ) * q ^ r

@[simp] theorem carryWeightedVerticalGreenKernel_zero (q : ℝ) :
    carryWeightedVerticalGreenKernel q 0 = 0 := by
  simp [carryWeightedVerticalGreenKernel]

theorem carryWeightedVerticalGreenKernel_nonneg
    {q : ℝ} (hq : 0 ≤ q) (r : ℕ) :
    0 ≤ carryWeightedVerticalGreenKernel q r := by
  unfold carryWeightedVerticalGreenKernel
  positivity

/-- Forma de duas coordenadas do mesmo nucleo. Para `j < k`, a entrada criada
na camada `j` chega a camada `k` com peso `(k-j) q^(k-j)`. -/
def carryConjugatedVerticalGreenKernel
    (q : ℝ) (k j : ℕ) : ℝ :=
  if j < k then carryWeightedVerticalGreenKernel q (k - j) else 0

@[simp] theorem carryConjugatedVerticalGreenKernel_of_lt
    (q : ℝ) {k j : ℕ} (hjk : j < k) :
    carryConjugatedVerticalGreenKernel q k j =
      carryWeightedVerticalGreenKernel q (k - j) := by
  simp [carryConjugatedVerticalGreenKernel, hjk]

@[simp] theorem carryConjugatedVerticalGreenKernel_of_not_lt
    (q : ℝ) {k j : ℕ} (hjk : ¬j < k) :
    carryConjugatedVerticalGreenKernel q k j = 0 := by
  simp [carryConjugatedVerticalGreenKernel, hjk]

/-- O fator polinomial `r` continua somavel depois de qualquer amortecimento
geometrico estrito `0 ≤ q < 1`. -/
theorem carryWeightedVerticalGreenKernel_summable
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (carryWeightedVerticalGreenKernel q) := by
  let a : ℝ := (q + 1) / 2
  have hqa : q < a := by
    dsimp [a]
    linarith
  have ha1 : a < 1 := by
    dsimp [a]
    linarith
  have ha0 : 0 ≤ a := by
    dsimp [a]
    linarith
  have hgeom : Summable (fun n : ℕ => a ^ n) :=
    summable_geometric_of_lt_one ha0 ha1
  have hnorm : ‖q‖ < a := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hqa
  have hlittle :
      (fun n : ℕ => (n : ℝ) * q ^ n) =o[atTop]
        (fun n : ℕ => a ^ n) := by
    simpa only [pow_one] using
      (isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt
        (R := ℝ) 1 hnorm)
  rcases hlittle.isBigO.exists_pos with ⟨C, _hCpos, hC⟩
  have hmajor : Summable (fun n : ℕ => C * a ^ n) :=
    hgeom.mul_left C
  refine hmajor.of_norm_bounded_eventually_nat ?_
  filter_upwards [hC.bound] with n hn
  simpa [carryWeightedVerticalGreenKernel, Real.norm_eq_abs,
    abs_of_nonneg hq0, abs_of_nonneg ha0] using hn

/-- Razao canonica entre amplitudes consecutivas na fibra de base `p`. -/
def primeCarryAmplitudeRatio (p : ℕ) : ℝ :=
  (Real.sqrt (p : ℝ))⁻¹

theorem primeCarryAmplitudeRatio_nonneg (p : ℕ) :
    0 ≤ primeCarryAmplitudeRatio p := by
  unfold primeCarryAmplitudeRatio
  positivity

/-- Para toda base material `p ≥ 2`, a razao de amplitude e estritamente
contrativa. -/
theorem primeCarryAmplitudeRatio_lt_one
    (p : ℕ) (hp : 2 ≤ p) :
    primeCarryAmplitudeRatio p < 1 := by
  have hpR : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hp)
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have hsqrt0 : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt (p : ℝ)) ^ 2 = (p : ℝ) :=
    Real.sq_sqrt hp0
  have hsqrt1 : 1 < Real.sqrt (p : ℝ) := by
    nlinarith
  have hsqrtPos : 0 < Real.sqrt (p : ℝ) :=
    lt_trans zero_lt_one hsqrt1
  unfold primeCarryAmplitudeRatio
  by_contra hnot
  have hge : 1 ≤ (Real.sqrt (p : ℝ))⁻¹ := le_of_not_gt hnot
  have hle :
      Real.sqrt (p : ℝ) ≤
        (Real.sqrt (p : ℝ))⁻¹ * Real.sqrt (p : ℝ) := by
    calc
      Real.sqrt (p : ℝ) = 1 * Real.sqrt (p : ℝ) := by rw [one_mul]
      _ ≤ (Real.sqrt (p : ℝ))⁻¹ * Real.sqrt (p : ℝ) :=
        mul_le_mul_of_nonneg_right hge hsqrt0
  rw [inv_mul_cancel₀ hsqrtPos.ne'] at hle
  exact (not_le_of_gt hsqrt1) hle

/-- Nucleo vertical especializado na amplitude de carry da base `p`. -/
def primeCarryWeightedVerticalGreenKernel (p : ℕ) (r : ℕ) : ℝ :=
  carryWeightedVerticalGreenKernel (primeCarryAmplitudeRatio p) r

theorem primeCarryWeightedVerticalGreenKernel_summable
    (p : ℕ) (hp : 2 ≤ p) :
    Summable (primeCarryWeightedVerticalGreenKernel p) := by
  simpa [primeCarryWeightedVerticalGreenKernel] using
    carryWeightedVerticalGreenKernel_summable
      (primeCarryAmplitudeRatio_nonneg p)
      (primeCarryAmplitudeRatio_lt_one p hp)

/-- Uma realizacao vertical e uma familia de shifts que nao aumentam norma.
A lei de semigrupo sera adicionada somente quando for necessaria para a
identidade completa de valvula; o bound Green usa apenas a contratilidade. -/
structure CarryVerticalShiftFamily (H : Type*)
    [NormedAddCommGroup H] [NormedSpace ℂ H] where
  shift : ℕ → H →L[ℂ] H
  norm_shift_le_one : ∀ r : ℕ, ‖shift r‖ ≤ 1

section ShiftFamily

variable {H : Type*}
variable [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- O termo de distancia `r` na serie operatorial do Green vestido. -/
def carryWeightedVerticalGreenTerm
    (S : CarryVerticalShiftFamily H) (q : ℝ) (r : ℕ) : H →L[ℂ] H :=
  (carryWeightedVerticalGreenKernel q r : ℂ) • S.shift r

theorem carryWeightedVerticalGreenTerm_norm_le
    (S : CarryVerticalShiftFamily H) {q : ℝ} (hq0 : 0 ≤ q) (r : ℕ) :
    ‖carryWeightedVerticalGreenTerm S q r‖ ≤
      carryWeightedVerticalGreenKernel q r := by
  have hk0 : 0 ≤ carryWeightedVerticalGreenKernel q r :=
    carryWeightedVerticalGreenKernel_nonneg hq0 r
  calc
    ‖carryWeightedVerticalGreenTerm S q r‖ ≤
        ‖(carryWeightedVerticalGreenKernel q r : ℂ)‖ * ‖S.shift r‖ := by
      rw [carryWeightedVerticalGreenTerm]
      exact norm_smul_le
        (carryWeightedVerticalGreenKernel q r : ℂ) (S.shift r)
    _ = carryWeightedVerticalGreenKernel q r * ‖S.shift r‖ := by
      simp [abs_of_nonneg hk0]
    _ ≤ carryWeightedVerticalGreenKernel q r * 1 :=
      mul_le_mul_of_nonneg_left (S.norm_shift_le_one r) hk0
    _ = carryWeightedVerticalGreenKernel q r := by ring

/-- A serie de operadores converge absolutamente sempre que `q < 1`. -/
theorem carryWeightedVerticalGreenTerm_summable
    [CompleteSpace H]
    (S : CarryVerticalShiftFamily H) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun r : ℕ => carryWeightedVerticalGreenTerm S q r) :=
  (carryWeightedVerticalGreenKernel_summable hq0 hq1).of_norm_bounded
    (fun r => carryWeightedVerticalGreenTerm_norm_le S hq0 r)

/-- Green vertical vestido como soma em norma de shifts contrativos. -/
def carryWeightedVerticalGreen
    (S : CarryVerticalShiftFamily H) (q : ℝ) : H →L[ℂ] H :=
  ∑' r : ℕ, carryWeightedVerticalGreenTerm S q r

/-- Bound de operador independente do cutoff. O lado direito e a massa `l1`
do nucleo vertical `r q^r`. -/
theorem carryWeightedVerticalGreen_norm_le_kernelMass
    (S : CarryVerticalShiftFamily H) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ‖carryWeightedVerticalGreen S q‖ ≤
      ∑' r : ℕ, carryWeightedVerticalGreenKernel q r := by
  have hk : Summable (carryWeightedVerticalGreenKernel q) :=
    carryWeightedVerticalGreenKernel_summable hq0 hq1
  have hnorm :
      Summable (fun r : ℕ => ‖carryWeightedVerticalGreenTerm S q r‖) :=
    Summable.of_nonneg_of_le
      (fun r => norm_nonneg (carryWeightedVerticalGreenTerm S q r))
      (fun r => carryWeightedVerticalGreenTerm_norm_le S hq0 r)
      hk
  rw [carryWeightedVerticalGreen]
  calc
    ‖∑' r : ℕ, carryWeightedVerticalGreenTerm S q r‖ ≤
        ∑' r : ℕ, ‖carryWeightedVerticalGreenTerm S q r‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' r : ℕ, carryWeightedVerticalGreenKernel q r :=
      hnorm.tsum_le_tsum
        (fun r => carryWeightedVerticalGreenTerm_norm_le S hq0 r) hk

/-- Green vertical vestido na base material `p`. -/
def primeCarryWeightedVerticalGreen
    (S : CarryVerticalShiftFamily H) (p : ℕ) : H →L[ℂ] H :=
  carryWeightedVerticalGreen S (primeCarryAmplitudeRatio p)

/-- O bound de cada base material e independente do cutoff e usa exatamente a
massa `l1` do nucleo `(r * p^(-r/2))`. -/
theorem primeCarryWeightedVerticalGreen_norm_le_kernelMass
    (S : CarryVerticalShiftFamily H) (p : ℕ) (hp : 2 ≤ p) :
    ‖primeCarryWeightedVerticalGreen S p‖ ≤
      ∑' r : ℕ, primeCarryWeightedVerticalGreenKernel p r := by
  simpa [primeCarryWeightedVerticalGreen,
    primeCarryWeightedVerticalGreenKernel] using
    carryWeightedVerticalGreen_norm_le_kernelMass S
      (primeCarryAmplitudeRatio_nonneg p)
      (primeCarryAmplitudeRatio_lt_one p hp)

/-- Corte finito da mesma serie. Ele usa exatamente o mesmo nucleo que o
operador infinito, sem renormalizacao dependente de `N`. -/
def carryWeightedVerticalGreenCutoff
    (S : CarryVerticalShiftFamily H) (q : ℝ) (N : ℕ) : H →L[ℂ] H :=
  ∑ r ∈ Finset.range N, carryWeightedVerticalGreenTerm S q r

theorem carryWeightedVerticalGreenCutoff_norm_le
    (S : CarryVerticalShiftFamily H) {q : ℝ} (hq0 : 0 ≤ q) (N : ℕ) :
    ‖carryWeightedVerticalGreenCutoff S q N‖ ≤
      ∑ r ∈ Finset.range N, carryWeightedVerticalGreenKernel q r := by
  unfold carryWeightedVerticalGreenCutoff
  calc
    ‖∑ r ∈ Finset.range N, carryWeightedVerticalGreenTerm S q r‖ ≤
        ∑ r ∈ Finset.range N, ‖carryWeightedVerticalGreenTerm S q r‖ :=
      norm_sum_le _ _
    _ ≤ ∑ r ∈ Finset.range N, carryWeightedVerticalGreenKernel q r := by
      gcongr with r hr
      exact carryWeightedVerticalGreenTerm_norm_le S hq0 r

end ShiftFamily

end

end CPFormal.Analytic.Cp
