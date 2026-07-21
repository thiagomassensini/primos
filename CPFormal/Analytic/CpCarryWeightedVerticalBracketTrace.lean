import CPFormal.Analytic.CpCarryL2UnilateralShift
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Bracket e traco verticais nas coordenadas de amplitude do carry

Este modulo transporta, no Hilbert vertical concreto, os dois operadores que
acompanham o Green:

* a segunda diferenca centrada, com a coordenada inicial reservada ao bordo;
* o traco exterior `(valor inicial, inclinacao inicial)`.

Se `x_k = q^k f_k`, as formulas transportadas sao

`B_q x(0) = 0`,
`B_q x(n+1) = q^(-1) x(n+2) - 2 x(n+1) + q x(n)`,

`Tr_q x = (x(0), q^(-1) x(1) - x(0))`.

O retorno ponderado e a identidade completa da valvula ficam para o modulo
seguinte. Nenhuma conclusao espectral e usada aqui.
-/

open scoped BigOperators lp ENNReal NNReal

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Avaliacao da coordenada `n` como mapa linear continuo em `ell^2`. -/
def carryVerticalL2EvalLinear (n : ℕ) : CarryVerticalL2 →ₗ[ℂ] ℂ where
  toFun x := x n
  map_add' x y := rfl
  map_smul' c x := rfl

/-- A avaliacao possui norma no maximo um. -/
def carryVerticalL2Eval (n : ℕ) : CarryVerticalL2 →L[ℂ] ℂ :=
  LinearMap.mkContinuous (carryVerticalL2EvalLinear n) 1
    (fun x => by
      change ‖x n‖ ≤ 1 * ‖x‖
      simpa using lp.norm_apply_le_norm (p := (2 : ℝ≥0∞))
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) x n)

@[simp] theorem carryVerticalL2Eval_apply
    (n : ℕ) (x : CarryVerticalL2) :
    carryVerticalL2Eval n x = x n := rfl

/-- Projecao que zera somente a coordenada inicial. Ela tipa o interior do
Green sem apagar nenhuma camada positiva. -/
def carryVerticalL2ZeroHeadProjection :
    CarryVerticalL2 →L[ℂ] CarryVerticalL2 :=
  ContinuousLinearMap.id ℂ CarryVerticalL2 -
    (ContinuousLinearMap.toSpanSingleton ℂ
        (lp.single 2 0 (1 : ℂ)) ∘L carryVerticalL2Eval 0)

@[simp] theorem carryVerticalL2ZeroHeadProjection_apply
    (x : CarryVerticalL2) (n : ℕ) :
    carryVerticalL2ZeroHeadProjection x n =
      if n = 0 then 0 else x n := by
  by_cases hn : n = 0
  · subst n
    simp [carryVerticalL2ZeroHeadProjection, lp.single_apply]
  · simp [carryVerticalL2ZeroHeadProjection, lp.single_apply, hn]

/-- Segunda diferenca centrada antes de reservar a coordenada de bordo. -/
def carryWeightedVerticalCenteredBracketCore (q : ℝ) :
    CarryVerticalL2 →L[ℂ] CarryVerticalL2 :=
  ((q : ℂ)⁻¹) • carryVerticalL2BackwardShift 1 -
    (2 : ℂ) • ContinuousLinearMap.id ℂ CarryVerticalL2 +
    (q : ℂ) • carryVerticalL2UnilateralShift 1

@[simp] theorem carryWeightedVerticalCenteredBracketCore_apply
    (q : ℝ) (x : CarryVerticalL2) (n : ℕ) :
    carryWeightedVerticalCenteredBracketCore q x n =
      (q : ℂ)⁻¹ * x (n + 1) - 2 * x n +
        (q : ℂ) * (if 1 ≤ n then x (n - 1) else 0) := by
  simp [carryWeightedVerticalCenteredBracketCore]

/-- Bracket vestido: a coordenada zero pertence ao reservatorio de bordo e o
interior comeca na primeira camada positiva. -/
def carryWeightedVerticalCenteredBracket (q : ℝ) :
    CarryVerticalL2 →L[ℂ] CarryVerticalL2 :=
  carryVerticalL2ZeroHeadProjection ∘L
    carryWeightedVerticalCenteredBracketCore q

@[simp] theorem carryWeightedVerticalCenteredBracket_zero
    (q : ℝ) (x : CarryVerticalL2) :
    carryWeightedVerticalCenteredBracket q x 0 = 0 := by
  simp [carryWeightedVerticalCenteredBracket]

@[simp] theorem carryWeightedVerticalCenteredBracket_succ
    (q : ℝ) (x : CarryVerticalL2) (n : ℕ) :
    carryWeightedVerticalCenteredBracket q x (n + 1) =
      (q : ℂ)⁻¹ * x (n + 2) - 2 * x (n + 1) +
        (q : ℂ) * x n := by
  simp [carryWeightedVerticalCenteredBracket, Nat.add_assoc]

/-- Traco vestido da valvula. Em coordenadas cruas ele corresponde a
`(f_0, f_1-f_0)`. -/
def carryWeightedVerticalTrace (q : ℝ) :
    CarryVerticalL2 →L[ℂ] (ℂ × ℂ) :=
  (carryVerticalL2Eval 0).prod
    (((q : ℂ)⁻¹) • carryVerticalL2Eval 1 - carryVerticalL2Eval 0)

@[simp] theorem carryWeightedVerticalTrace_apply
    (q : ℝ) (x : CarryVerticalL2) :
    carryWeightedVerticalTrace q x =
      (x 0, (q : ℂ)⁻¹ * x 1 - x 0) := by
  simp [carryWeightedVerticalTrace]

/-- Bracket material da base `p`. -/
def primeCarryWeightedVerticalCenteredBracket (p : ℕ) :
    CarryVerticalL2 →L[ℂ] CarryVerticalL2 :=
  carryWeightedVerticalCenteredBracket (primeCarryAmplitudeRatio p)

/-- Traco material da base `p`. -/
def primeCarryWeightedVerticalTrace (p : ℕ) :
    CarryVerticalL2 →L[ℂ] (ℂ × ℂ) :=
  carryWeightedVerticalTrace (primeCarryAmplitudeRatio p)

end

end CPFormal.Analytic.Cp
