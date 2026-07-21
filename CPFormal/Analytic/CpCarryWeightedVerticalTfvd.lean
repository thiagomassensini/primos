import CPFormal.Analytic.CpCarryWeightedVerticalReturn

/-!
# Identidade TFVD vertical ponderada

Este modulo abre o Green vestido coordenada por coordenada. Como o shift
unilateral de distancia `r` zera a coordenada `n` quando `r > n`, a serie
operatorial infinita reduz-se, em cada coordenada, a uma soma finita.

A formula coordenada e a entrada para provar a identidade completa da valvula

`G_q B_q + R_q Tr_q = I`.

Nenhuma conclusao espectral e usada aqui.
-/

open scoped BigOperators lp ENNReal NNReal

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Avaliacao de um operador continuo num vetor fixo, como mapa linear
continuo no espaco de operadores. -/
def carryVerticalL2OperatorApply (x : CarryVerticalL2) :
    (CarryVerticalL2 →L[ℂ] CarryVerticalL2) →L[ℂ] CarryVerticalL2 :=
  LinearMap.mkContinuous
    { toFun := fun T => T x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    ‖x‖
    (fun T => by
      simpa [mul_comm] using T.le_opNorm x)

@[simp] theorem carryVerticalL2OperatorApply_apply
    (x : CarryVerticalL2) (T : CarryVerticalL2 →L[ℂ] CarryVerticalL2) :
    carryVerticalL2OperatorApply x T = T x := rfl

/-- Avaliacao conjunta de um operador no vetor `x` e na coordenada `n`. -/
def carryVerticalL2OperatorCoordinate
    (x : CarryVerticalL2) (n : ℕ) :
    (CarryVerticalL2 →L[ℂ] CarryVerticalL2) →L[ℂ] ℂ :=
  carryVerticalL2Eval n ∘L carryVerticalL2OperatorApply x

@[simp] theorem carryVerticalL2OperatorCoordinate_apply
    (x : CarryVerticalL2) (n : ℕ)
    (T : CarryVerticalL2 →L[ℂ] CarryVerticalL2) :
    carryVerticalL2OperatorCoordinate x n T = T x n := rfl

/-- Em cada coordenada, a serie Green torna-se a convolucao causal finita
`sum_{r <= n} r q^r x_{n-r}`. -/
theorem carryVerticalL2WeightedGreen_apply
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (x : CarryVerticalL2) (n : ℕ) :
    carryVerticalL2WeightedGreen q x n =
      ∑ r ∈ Finset.range (n + 1),
        (carryWeightedVerticalGreenKernel q r : ℂ) * x (n - r) := by
  have hsum : Summable (fun r : ℕ =>
      carryWeightedVerticalGreenTerm carryVerticalL2ShiftFamily q r) :=
    carryWeightedVerticalGreenTerm_summable
      carryVerticalL2ShiftFamily hq0 hq1
  rw [carryVerticalL2WeightedGreen, carryWeightedVerticalGreen]
  change
    carryVerticalL2OperatorCoordinate x n
        (∑' r : ℕ,
          carryWeightedVerticalGreenTerm carryVerticalL2ShiftFamily q r) = _
  rw [(carryVerticalL2OperatorCoordinate x n).map_tsum hsum]
  rw [tsum_eq_sum (s := Finset.range (n + 1)) (fun r hr => by
    have hrnot : ¬r ≤ n := by omega
    simp [carryWeightedVerticalGreenTerm, carryVerticalL2ShiftFamily,
      carryVerticalL2UnilateralShift_apply, hrnot])]
  apply Finset.sum_congr rfl
  intro r hr
  have hrle : r ≤ n := by omega
  simp [carryWeightedVerticalGreenTerm, carryVerticalL2ShiftFamily,
    carryVerticalL2UnilateralShift_apply, hrle]

end

end CPFormal.Analytic.Cp
