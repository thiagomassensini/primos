import CPFormal.Analytic.CpCarryWeightedVerticalTfvd
import CPFormal.Analytic.CpFiniteGreen

/-!
# Telescopagem finita da valvula vertical ponderada

Este modulo isola a identidade escalar que governa a valvula. A primeira
diferenca ponderada e

`d_q x(n) = q^(-1) x(n+1) - x(n)`.

A segunda diferenca e `d_q x(n+1) - q d_q x(n)`. O Green triangular soma essa
segunda diferenca e reconstrui o estado a partir dela e do traco inicial.
-/

open scoped BigOperators

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Primeira diferenca nas coordenadas de amplitude. -/
def carryWeightedScalarFirstDifference
    (q : ℂ) (x : ℕ → ℂ) (n : ℕ) : ℂ :=
  q⁻¹ * x (n + 1) - x n

/-- Segunda diferenca ponderada, escrita como diferenca de primeiras
diferencas consecutivas. -/
def carryWeightedScalarSecondDifference
    (q : ℂ) (x : ℕ → ℂ) (n : ℕ) : ℂ :=
  carryWeightedScalarFirstDifference q x (n + 1) -
    q * carryWeightedScalarFirstDifference q x n

/-- Forma expandida da segunda diferenca ponderada. -/
theorem carryWeightedScalarSecondDifference_eq
    {q : ℂ} (hq : q ≠ 0) (x : ℕ → ℂ) (n : ℕ) :
    carryWeightedScalarSecondDifference q x n =
      q⁻¹ * x (n + 2) - 2 * x (n + 1) + q * x n := by
  unfold carryWeightedScalarSecondDifference
    carryWeightedScalarFirstDifference
  simp only [Nat.add_assoc]
  field_simp [hq]
  ring

/-- Soma Green finita da segunda diferenca ponderada. -/
def carryWeightedScalarGreenSum
    (q : ℂ) (x : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range n,
    ((n - 1 - j : ℕ) : ℂ) * q ^ (n - 1 - j) *
      carryWeightedScalarSecondDifference q x j

/-- A soma geometricamente ponderada das segundas diferencas telescopa para os
dois endpoints da primeira diferenca. -/
theorem carryWeightedScalarSecondDifference_telescope
    (q : ℂ) (x : ℕ → ℂ) (n : ℕ) :
    (∑ j ∈ Finset.range n,
      q ^ (n - 1 - j) * carryWeightedScalarSecondDifference q x j) =
        carryWeightedScalarFirstDifference q x n -
          q ^ n * carryWeightedScalarFirstDifference q x 0 := by
  let d : ℕ → ℂ := fun k => carryWeightedScalarFirstDifference q x k
  let F : ℕ → ℂ := fun k => q ^ (n - k) * d k
  calc
    (∑ j ∈ Finset.range n,
      q ^ (n - 1 - j) * carryWeightedScalarSecondDifference q x j) =
        ∑ j ∈ Finset.range n, (F (j + 1) - F j) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjlt : j < n := Finset.mem_range.mp hj
          have hleft : n - (j + 1) = n - 1 - j := by omega
          have hright : n - j = (n - 1 - j) + 1 := by omega
          dsimp [F, d, carryWeightedScalarSecondDifference]
          rw [hleft, hright, pow_succ]
          ring
    _ = F (0 + n) - F 0 := by
      simpa using (sum_range_forwardDifference F 0 n)
    _ = carryWeightedScalarFirstDifference q x n -
          q ^ n * carryWeightedScalarFirstDifference q x 0 := by
      simp [F, d]

/-- Ao aumentar o endpoint em uma unidade, a soma Green satisfaz a recorrencia
causal esperada. -/
theorem carryWeightedScalarGreenSum_succ
    (q : ℂ) (x : ℕ → ℂ) (n : ℕ) :
    carryWeightedScalarGreenSum q x (n + 1) =
      q * carryWeightedScalarGreenSum q x n +
        q * (carryWeightedScalarFirstDifference q x n -
          q ^ n * carryWeightedScalarFirstDifference q x 0) := by
  rw [← carryWeightedScalarSecondDifference_telescope q x n]
  unfold carryWeightedScalarGreenSum
  rw [Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel, Nat.sub_self, Nat.cast_zero,
    zero_mul, add_zero]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < n := Finset.mem_range.mp hj
  have hsub : n - j = (n - 1 - j) + 1 := by omega
  rw [hsub, pow_succ]
  push_cast
  ring

/-- Teorema fundamental escalar da valvula ponderada. -/
theorem carryWeightedScalarReconstruction
    {q : ℂ} (hq : q ≠ 0) (x : ℕ → ℂ) (n : ℕ) :
    x n =
      q ^ n *
          (x 0 + (n : ℂ) * carryWeightedScalarFirstDifference q x 0) +
        carryWeightedScalarGreenSum q x n := by
  induction n with
  | zero =>
      simp [carryWeightedScalarGreenSum]
  | succ n ih =>
      calc
        x (n + 1) =
            q * x n + q * carryWeightedScalarFirstDifference q x n := by
              unfold carryWeightedScalarFirstDifference
              field_simp [hq]
              ring
        _ = q *
              (q ^ n *
                  (x 0 + (n : ℂ) *
                    carryWeightedScalarFirstDifference q x 0) +
                carryWeightedScalarGreenSum q x n) +
              q * carryWeightedScalarFirstDifference q x n := by
                rw [ih]
        _ = q ^ (n + 1) *
              (x 0 + ((n + 1 : ℕ) : ℂ) *
                carryWeightedScalarFirstDifference q x 0) +
              carryWeightedScalarGreenSum q x (n + 1) := by
                rw [carryWeightedScalarGreenSum_succ]
                rw [pow_succ]
                push_cast
                ring

end

end CPFormal.Analytic.Cp
