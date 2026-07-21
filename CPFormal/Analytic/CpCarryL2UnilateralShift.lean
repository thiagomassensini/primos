import CPFormal.Analytic.CpCarryWeightedVerticalGreen
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Shift unilateral vertical no espaco de amplitudes do carry

Este modulo realiza a familia abstrata de shifts usada pelo Green vestido no
Hilbert vertical canonico `ell^2(N, C)`.

A construcao e feita em duas etapas:

* o tail-shift `B_r x(n) = x(n+r)` e construido diretamente e provado
  contrativo pela decomposicao da serie quadratica em cabeca mais cauda;
* o shift causal `S_r` e definido como o adjunto de `B_r`.

Assim o operador Green da camada anterior passa a agir num espaco de Hilbert
concreto. Nenhuma identidade de bordo e declarada neste arquivo: bracket,
traco e retorno ainda precisam ser transportados de forma coordenada.
-/

open scoped BigOperators lp ENNReal NNReal

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Hilbert vertical de amplitudes indexadas pela profundidade de carry. -/
abbrev CarryVerticalL2 := ℓ²(ℕ, ℂ)

/-- Tail-shift linear: remove as primeiras `r` coordenadas. -/
def carryVerticalL2BackwardShiftLinear (r : ℕ) :
    CarryVerticalL2 →ₗ[ℂ] CarryVerticalL2 where
  toFun x :=
    ⟨fun n => x (n + r), by
      change Memℓp (fun n : ℕ => x (n + r)) 2
      rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
      exact (summable_nat_add_iff r).2
        ((lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))⟩
  map_add' x y := by
    ext n
    rfl
  map_smul' c x := by
    ext n
    rfl

@[simp] theorem carryVerticalL2BackwardShiftLinear_apply
    (r : ℕ) (x : CarryVerticalL2) (n : ℕ) :
    carryVerticalL2BackwardShiftLinear r x n = x (n + r) := rfl

/-- Remover uma cabeca finita nao aumenta a norma `ell^2`. -/
theorem carryVerticalL2BackwardShiftLinear_norm_le
    (r : ℕ) (x : CarryVerticalL2) :
    ‖carryVerticalL2BackwardShiftLinear r x‖ ≤ ‖x‖ := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  rw [← Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hp]
  rw [lp.norm_rpow_eq_tsum hp, lp.norm_rpow_eq_tsum hp]
  simp only [carryVerticalL2BackwardShiftLinear_apply]
  have hx : Summable (fun n : ℕ => ‖x n‖ ^ (2 : ℝ≥0∞).toReal) :=
    (lp.memℓp x).summable hp
  have hsplit := hx.sum_add_tsum_nat_add r
  rw [← hsplit]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun n hn => by positivity)

/-- Tail-shift como operador linear continuo contrativo. -/
def carryVerticalL2BackwardShift (r : ℕ) :
    CarryVerticalL2 →L[ℂ] CarryVerticalL2 :=
  LinearMap.mkContinuous (carryVerticalL2BackwardShiftLinear r) 1
    (fun x => by
      change ‖carryVerticalL2BackwardShiftLinear r x‖ ≤ 1 * ‖x‖
      simpa using carryVerticalL2BackwardShiftLinear_norm_le r x)

@[simp] theorem carryVerticalL2BackwardShift_apply
    (r : ℕ) (x : CarryVerticalL2) (n : ℕ) :
    carryVerticalL2BackwardShift r x n = x (n + r) := rfl

theorem carryVerticalL2BackwardShift_norm_le_one (r : ℕ) :
    ‖carryVerticalL2BackwardShift r‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro x
  change ‖carryVerticalL2BackwardShiftLinear r x‖ ≤ 1 * ‖x‖
  simpa using carryVerticalL2BackwardShiftLinear_norm_le r x

/-- O tail-shift leva o vetor elementar `e_k` a `e_(k-r)` quando esse indice
existe, e a zero caso contrario. -/
theorem carryVerticalL2BackwardShift_single (r k : ℕ) :
    carryVerticalL2BackwardShift r (lp.single 2 k (1 : ℂ)) =
      if r ≤ k then lp.single 2 (k - r) (1 : ℂ) else 0 := by
  ext n
  by_cases hrk : r ≤ k
  · have hiff : n + r = k ↔ n = k - r := by omega
    simp [carryVerticalL2BackwardShift_apply, lp.single_apply,
      Pi.single_apply, hrk, hiff]
  · have hne : n + r ≠ k := by omega
    simp [carryVerticalL2BackwardShift_apply, lp.single_apply,
      Pi.single_apply, hrk, hne]

/-- Shift unilateral causal, definido como adjunto do tail-shift. -/
def carryVerticalL2UnilateralShift (r : ℕ) :
    CarryVerticalL2 →L[ℂ] CarryVerticalL2 :=
  ContinuousLinearMap.adjoint (carryVerticalL2BackwardShift r)

/-- Formula coordenada do shift unilateral: insere `r` zeros no inicio. -/
@[simp] theorem carryVerticalL2UnilateralShift_apply
    (r : ℕ) (x : CarryVerticalL2) (n : ℕ) :
    carryVerticalL2UnilateralShift r x n =
      if r ≤ n then x (n - r) else 0 := by
  have hinner :
      inner ℂ (lp.single 2 n (1 : ℂ))
          (carryVerticalL2UnilateralShift r x) =
        inner ℂ
          (carryVerticalL2BackwardShift r (lp.single 2 n (1 : ℂ))) x := by
    exact ContinuousLinearMap.adjoint_inner_right
      (carryVerticalL2BackwardShift r) (lp.single 2 n (1 : ℂ)) x
  by_cases hrn : r ≤ n
  · simpa [carryVerticalL2UnilateralShift,
      carryVerticalL2BackwardShift_single, hrn, lp.inner_single_left] using hinner
  · simpa [carryVerticalL2UnilateralShift,
      carryVerticalL2BackwardShift_single, hrn, lp.inner_single_left] using hinner

/-- O shift unilateral e contrativo; de fato, o adjunto preserva a norma de
operador. -/
theorem carryVerticalL2UnilateralShift_norm_le_one (r : ℕ) :
    ‖carryVerticalL2UnilateralShift r‖ ≤ 1 := by
  calc
    ‖carryVerticalL2UnilateralShift r‖ =
        ‖carryVerticalL2BackwardShift r‖ :=
      ContinuousLinearMap.adjoint.norm_map _
    _ ≤ 1 := carryVerticalL2BackwardShift_norm_le_one r

/-- Familia concreta de shifts verticais usada pelo Green vestido. -/
def carryVerticalL2ShiftFamily : CarryVerticalShiftFamily CarryVerticalL2 where
  shift := carryVerticalL2UnilateralShift
  norm_shift_le_one := carryVerticalL2UnilateralShift_norm_le_one

/-- Green vertical vestido, agora realizado em `ell^2(N,C)`. -/
def carryVerticalL2WeightedGreen (q : ℝ) :
    CarryVerticalL2 →L[ℂ] CarryVerticalL2 :=
  carryWeightedVerticalGreen carryVerticalL2ShiftFamily q

/-- Especializacao material da base `p`. -/
def primeCarryVerticalL2WeightedGreen (p : ℕ) :
    CarryVerticalL2 →L[ℂ] CarryVerticalL2 :=
  primeCarryWeightedVerticalGreen carryVerticalL2ShiftFamily p

/-- Bound concreto, independente do cutoff, no Hilbert vertical natural. -/
theorem primeCarryVerticalL2WeightedGreen_norm_le_kernelMass
    (p : ℕ) (hp : 2 ≤ p) :
    ‖primeCarryVerticalL2WeightedGreen p‖ ≤
      ∑' r : ℕ, primeCarryWeightedVerticalGreenKernel p r := by
  exact primeCarryWeightedVerticalGreen_norm_le_kernelMass
    carryVerticalL2ShiftFamily p hp

end

end CPFormal.Analytic.Cp
