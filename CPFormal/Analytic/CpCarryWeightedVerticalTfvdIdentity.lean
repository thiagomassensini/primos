import CPFormal.Analytic.CpCarryWeightedVerticalTfvdFinite

/-!
# Identidade completa da valvula vertical ponderada

A telescopagem finita e agora identificada com os operadores concretos no
Hilbert vertical. O resultado principal e

`G_q B_q + R_q Tr_q = I`.

A prova ocorre coordenada por coordenada e depois e promovida a igualdade de
operadores lineares continuos.
-/

open scoped BigOperators lp ENNReal NNReal

namespace CPFormal.Analytic.Cp

noncomputable section

/-- O Green concreto aplicado ao bracket coincide com a soma Green finita da
identidade escalar. -/
theorem carryVerticalL2WeightedGreen_bracket_apply
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (x : CarryVerticalL2) (n : ℕ) :
    carryVerticalL2WeightedGreen q
        (carryWeightedVerticalCenteredBracket q x) n =
      carryWeightedScalarGreenSum (q : ℂ) x n := by
  rw [carryVerticalL2WeightedGreen_apply_reindexed q hqpos.le hq1]
  rw [Finset.sum_range_succ']
  simp only [carryWeightedVerticalCenteredBracket_zero, mul_zero, add_zero]
  unfold carryWeightedScalarGreenSum
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < n := Finset.mem_range.mp hj
  have hsub : n - (j + 1) = n - 1 - j := by omega
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hqpos.ne'
  rw [hsub, carryWeightedVerticalCenteredBracket_succ,
    carryWeightedScalarSecondDifference_eq hqC]
  simp [carryWeightedVerticalGreenKernel]

/-- Forma coordenada da identidade completa da valvula ponderada. -/
theorem carryWeightedVerticalTfvd_apply
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (x : CarryVerticalL2) (n : ℕ) :
    carryVerticalL2WeightedGreen q
          (carryWeightedVerticalCenteredBracket q x) n +
        carryWeightedVerticalReturn q hqpos.le hq1
          (carryWeightedVerticalTrace q x) n =
      x n := by
  rw [carryVerticalL2WeightedGreen_bracket_apply q hqpos hq1]
  rw [carryWeightedVerticalReturn_apply,
    carryWeightedVerticalTrace_apply]
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hqpos.ne'
  have hrec := carryWeightedScalarReconstruction
    (q := (q : ℂ)) hqC (fun k => x k) n
  simpa [carryWeightedScalarFirstDifference, add_comm] using hrec.symm

/-- Teorema Fundamental da Valvula Discreta nas coordenadas verticais de
amplitude. -/
theorem carryWeightedVerticalTfvd_identity
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    carryVerticalL2WeightedGreen q ∘L
          carryWeightedVerticalCenteredBracket q +
        carryWeightedVerticalReturn q hqpos.le hq1 ∘L
          carryWeightedVerticalTrace q =
      ContinuousLinearMap.id ℂ CarryVerticalL2 := by
  apply ContinuousLinearMap.ext
  intro x
  ext n
  simpa using carryWeightedVerticalTfvd_apply q hqpos hq1 x n

/-- Especializacao da identidade completa a toda base material `p >= 2`. -/
theorem primeCarryWeightedVerticalTfvd_identity
    (p : ℕ) (hp : 2 ≤ p) :
    primeCarryVerticalL2WeightedGreen p ∘L
          primeCarryWeightedVerticalCenteredBracket p +
        primeCarryWeightedVerticalReturn p hp ∘L
          primeCarryWeightedVerticalTrace p =
      ContinuousLinearMap.id ℂ CarryVerticalL2 := by
  simpa [primeCarryVerticalL2WeightedGreen,
    primeCarryWeightedVerticalGreen,
    carryVerticalL2WeightedGreen,
    primeCarryWeightedVerticalCenteredBracket,
    primeCarryWeightedVerticalReturn,
    primeCarryWeightedVerticalTrace] using
      carryWeightedVerticalTfvd_identity
        (primeCarryAmplitudeRatio p)
        (primeCarryAmplitudeRatio_pos p (by omega))
        (primeCarryAmplitudeRatio_lt_one p hp)

end

end CPFormal.Analytic.Cp
