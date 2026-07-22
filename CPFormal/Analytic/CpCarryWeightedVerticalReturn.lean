import CPFormal.Analytic.CpCarryWeightedVerticalBracketTrace
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Retorno afim vestido pela amplitude do carry

Para `0 <= q < 1`, este modulo constroi no Hilbert vertical os dois modos de
bordo

`g_q(k) = q^k`,
`h_q(k) = k q^k`,

e o retorno continuo

`R_q(a,b)(k) = q^k (a + k b)`.

O kernel prova tambem as duas identidades de valvula que dependem somente do
bordo:

`Tr_q R_q = I`,
`B_q R_q = 0`.

A identidade complementar `G_q B_q + R_q Tr_q = I` fica separada para que a
passagem da serie Green a coordenadas seja auditada explicitamente.
-/

open scoped BigOperators lp ENNReal NNReal

namespace CPFormal.Analytic.Cp

noncomputable section

/-- O modo geometrico `q^k` pertence a `ell^2` para `0 <= q < 1`. -/
def carryGeometricAmplitudeVector
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) : CarryVerticalL2 :=
  ⟨fun n : ℕ => (q : ℂ) ^ n, by
    have hsum : Summable (fun n : ℕ => ‖(q : ℂ) ^ n‖) := by
      simpa [norm_pow, abs_of_nonneg hq0] using
        (summable_geometric_of_lt_one hq0 hq1)
    have hmem1 : Memℓp (fun n : ℕ => (q : ℂ) ^ n) 1 := by
      rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
      simpa using hsum
    exact hmem1.of_exponent_ge (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩

@[simp] theorem carryGeometricAmplitudeVector_apply
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    carryGeometricAmplitudeVector q hq0 hq1 n = (q : ℂ) ^ n := rfl

/-- O modo de inclinacao `k q^k` pertence a `ell^2`. Sua somabilidade `ell^1`
ja foi provada pelo majorante do Green. -/
def carryAffineSlopeAmplitudeVector
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) : CarryVerticalL2 :=
  ⟨fun n : ℕ => (carryWeightedVerticalGreenKernel q n : ℂ), by
    have hsumReal : Summable (carryWeightedVerticalGreenKernel q) :=
      carryWeightedVerticalGreenKernel_summable hq0 hq1
    have hsumNorm : Summable
        (fun n : ℕ => ‖(carryWeightedVerticalGreenKernel q n : ℂ)‖) := by
      refine hsumReal.congr ?_
      intro n
      simp [abs_of_nonneg
        (carryWeightedVerticalGreenKernel_nonneg hq0 n)]
    have hmem1 : Memℓp
        (fun n : ℕ => (carryWeightedVerticalGreenKernel q n : ℂ)) 1 := by
      rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
      simpa using hsumNorm
    exact hmem1.of_exponent_ge (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩

@[simp] theorem carryAffineSlopeAmplitudeVector_apply
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    carryAffineSlopeAmplitudeVector q hq0 hq1 n =
      (carryWeightedVerticalGreenKernel q n : ℂ) := rfl

/-- Retorno afim vestido. A continuidade e automatica porque ele e uma soma
de dois mapas de posto um gerados por vetores de `ell^2`. -/
def carryWeightedVerticalReturn
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (ℂ × ℂ) →L[ℂ] CarryVerticalL2 :=
  (ContinuousLinearMap.toSpanSingleton ℂ
      (carryGeometricAmplitudeVector q hq0 hq1) ∘L
        ContinuousLinearMap.fst ℂ ℂ ℂ) +
  (ContinuousLinearMap.toSpanSingleton ℂ
      (carryAffineSlopeAmplitudeVector q hq0 hq1) ∘L
        ContinuousLinearMap.snd ℂ ℂ ℂ)

@[simp] theorem carryWeightedVerticalReturn_apply
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (boundary : ℂ × ℂ) (n : ℕ) :
    carryWeightedVerticalReturn q hq0 hq1 boundary n =
      (q : ℂ) ^ n * (boundary.1 + (n : ℂ) * boundary.2) := by
  rcases boundary with ⟨a, b⟩
  simp [carryWeightedVerticalReturn,
    carryWeightedVerticalGreenKernel]
  ring

/-- O traco vestido recupera exatamente os dois dados de bordo. -/
theorem carryWeightedVerticalTrace_comp_return
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    carryWeightedVerticalTrace q ∘L
        carryWeightedVerticalReturn q hqpos.le hq1 =
      ContinuousLinearMap.id ℂ (ℂ × ℂ) := by
  apply ContinuousLinearMap.ext
  intro boundary
  rcases boundary with ⟨a, b⟩
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hqpos.ne'
  apply Prod.ext
  · simp
  · simp [hqC]

/-- O bracket vestido e cego ao retorno afim vestido. -/
theorem carryWeightedVerticalCenteredBracket_comp_return
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    carryWeightedVerticalCenteredBracket q ∘L
        carryWeightedVerticalReturn q hqpos.le hq1 = 0 := by
  apply ContinuousLinearMap.ext
  intro boundary
  rcases boundary with ⟨a, b⟩
  ext n
  cases n with
  | zero => simp
  | succ n =>
      have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hqpos.ne'
      change
        carryWeightedVerticalCenteredBracket q
            (carryWeightedVerticalReturn q hqpos.le hq1 (a, b)) (n + 1) = 0
      rw [carryWeightedVerticalCenteredBracket_succ]
      simp only [carryWeightedVerticalReturn_apply]
      simp only [pow_succ]
      field_simp [hqC]
      push_cast
      ring

/-- A razao material de amplitude e estritamente positiva. -/
theorem primeCarryAmplitudeRatio_pos
    (p : ℕ) (hp : 1 ≤ p) :
    0 < primeCarryAmplitudeRatio p := by
  have hpNat : 0 < p := lt_of_lt_of_le Nat.zero_lt_one hp
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpNat
  unfold primeCarryAmplitudeRatio
  exact inv_pos.mpr (Real.sqrt_pos.2 hpR)

/-- Retorno vestido especializado na base material `p`. -/
def primeCarryWeightedVerticalReturn
    (p : ℕ) (hp : 2 ≤ p) :
    (ℂ × ℂ) →L[ℂ] CarryVerticalL2 :=
  carryWeightedVerticalReturn (primeCarryAmplitudeRatio p)
    (primeCarryAmplitudeRatio_nonneg p)
    (primeCarryAmplitudeRatio_lt_one p hp)

/-- Na base material, o traco do retorno tambem e a identidade. -/
theorem primeCarryWeightedVerticalTrace_comp_return
    (p : ℕ) (hp : 2 ≤ p) :
    primeCarryWeightedVerticalTrace p ∘L
        primeCarryWeightedVerticalReturn p hp =
      ContinuousLinearMap.id ℂ (ℂ × ℂ) := by
  exact carryWeightedVerticalTrace_comp_return
    (primeCarryAmplitudeRatio p)
    (primeCarryAmplitudeRatio_pos p (by omega))
    (primeCarryAmplitudeRatio_lt_one p hp)

/-- Na base material, o bracket aniquila o retorno. -/
theorem primeCarryWeightedVerticalCenteredBracket_comp_return
    (p : ℕ) (hp : 2 ≤ p) :
    primeCarryWeightedVerticalCenteredBracket p ∘L
        primeCarryWeightedVerticalReturn p hp = 0 := by
  exact carryWeightedVerticalCenteredBracket_comp_return
    (primeCarryAmplitudeRatio p)
    (primeCarryAmplitudeRatio_pos p (by omega))
    (primeCarryAmplitudeRatio_lt_one p hp)

end

end CPFormal.Analytic.Cp
