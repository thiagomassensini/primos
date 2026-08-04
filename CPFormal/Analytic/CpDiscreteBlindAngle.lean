import CPFormal.Carry.CpBranchWeight
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.Order.Chebyshev

/-!
# O ângulo cego do discreto

Cristaliza a leitura do laboratório numérico: o fenômeno **não** é de análise
complexa nem de primos — é o ângulo cego que somas discretas de massa unitária
têm ao sondar o contínuo.  Tudo aqui vale num espaço normado real **qualquer**
`E` (invariante de representação: não importa se `ℝ²`, `ℂ`, ou outro).

Sejam `v : Fin N → E` as coordenadas discretas (massas unitárias com direção).

* `discreteResultant v = ∑ᵢ vᵢ`   — o observável escalar (visível);
* `discreteEnergy v = ∑ᵢ ‖vᵢ‖²`   — a energia total;
* `visibleEnergy v = ‖resultante‖²/N`,  `hiddenEnergy = total − visível`.

Resultados:

* `visibleEnergy_le_totalEnergy` — o visível nunca excede o total (o `score ∈
  [0,1]` do laboratório), por Cauchy–Schwarz;
* `hiddenEnergy_eq_total_of_resultant_zero` — **no ângulo cego** (`resultante =
  0`) a energia oculta **é** a energia total: a energia não some, fica ortogonal
  ao escalar;
* `exists_blindAngle` — o ângulo cego existe: há configuração de energia
  estritamente positiva com resultante nulo;
* `discrete_blindAngle_carry` — com amplitude de massa unitária do carry, o
  ângulo cego deixa energia `2·criticalMass p k`, com a **mesma** estrutura para
  toda base `p` (invariante de régua, via `criticalAmplitude_sq_eq_mass`).

Genuine First: nenhum zeta, equação funcional ou RH.
-/

namespace CPFormal.Analytic.Cp

open scoped BigOperators
open CPFormal.Carry.Cp

variable {E : Type*} [NormedAddCommGroup E]

/-- Resultante escalar (visível) de uma configuração discreta finita. -/
def discreteResultant {N : ℕ} (v : Fin N → E) : E := ∑ i, v i

/-- Energia total (soma das massas unitárias). -/
def discreteEnergy {N : ℕ} (v : Fin N → E) : ℝ := ∑ i, ‖v i‖ ^ 2

/-- Energia visível ao observador escalar: `‖resultante‖²/N`. -/
noncomputable def visibleEnergy {N : ℕ} (v : Fin N → E) : ℝ :=
  ‖discreteResultant v‖ ^ 2 / N

/-- Energia oculta: o que o escalar não vê. -/
noncomputable def hiddenEnergy {N : ℕ} (v : Fin N → E) : ℝ :=
  discreteEnergy v - visibleEnergy v

/-- **Cota do ângulo cego (Cauchy–Schwarz).**  `‖resultante‖² ≤ N · energia`.  É o
`score ∈ [0,1]` do laboratório: o visível nunca excede o total. -/
theorem discreteResultant_normSq_le {N : ℕ} (v : Fin N → E) :
    ‖discreteResultant v‖ ^ 2 ≤ (N : ℝ) * discreteEnergy v := by
  have htri : ‖(∑ i, v i)‖ ≤ ∑ i, ‖v i‖ := norm_sum_le _ _
  have h0 : 0 ≤ ‖(∑ i, v i)‖ := norm_nonneg _
  have hsq : ‖(∑ i, v i)‖ ^ 2 ≤ (∑ i, ‖v i‖) ^ 2 := by nlinarith [htri, h0]
  have hcs : (∑ i, ‖v i‖) ^ 2 ≤
      ((Finset.univ : Finset (Fin N)).card : ℝ) * ∑ i, ‖v i‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  calc ‖discreteResultant v‖ ^ 2 = ‖(∑ i, v i)‖ ^ 2 := rfl
    _ ≤ (∑ i, ‖v i‖) ^ 2 := hsq
    _ ≤ ((Finset.univ : Finset (Fin N)).card : ℝ) * ∑ i, ‖v i‖ ^ 2 := hcs
    _ = (N : ℝ) * discreteEnergy v := by
        rw [Finset.card_univ, Fintype.card_fin]; rfl

/-- O visível nunca excede o total. -/
theorem visibleEnergy_le_totalEnergy {N : ℕ} (hN : 0 < N) (v : Fin N → E) :
    visibleEnergy v ≤ discreteEnergy v := by
  rw [visibleEnergy, div_le_iff₀ (by exact_mod_cast hN)]
  have := discreteResultant_normSq_le v
  linarith [this]

/-- **A energia oculta no zero é a energia total.**  No ângulo cego (resultante
nulo) toda a energia permanece — invisível ao escalar, ortogonal a ele. -/
theorem hiddenEnergy_eq_total_of_resultant_zero {N : ℕ} (v : Fin N → E)
    (h : discreteResultant v = 0) :
    hiddenEnergy v = discreteEnergy v := by
  rw [hiddenEnergy, visibleEnergy, h, norm_zero]
  simp

/-- **O ângulo cego existe.**  Há configuração discreta de energia estritamente
positiva cujo resultante escalar é zero: a energia se esconde ortogonalmente. -/
theorem exists_blindAngle (u : E) (hu : u ≠ 0) :
    ∃ (N : ℕ) (v : Fin N → E), discreteResultant v = 0 ∧ 0 < discreteEnergy v := by
  refine ⟨2, ![u, -u], ?_, ?_⟩
  · simp [discreteResultant, Fin.sum_univ_two]
  · have hval : discreteEnergy ![u, -u] = 2 * ‖u‖ ^ 2 := by
      simp only [discreteEnergy, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, norm_neg]; ring
    rw [hval]
    have : 0 < ‖u‖ := norm_pos_iff.mpr hu
    nlinarith [this]

/-- Energia do par cego em função da norma: `2‖u‖²`. -/
theorem blindAngle_energy_eq_two_normSq (u : E) :
    discreteEnergy ![u, -u] = 2 * ‖u‖ ^ 2 := by
  simp only [discreteEnergy, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, norm_neg]; ring

/-- **Ângulo cego do carry, invariante de régua.**  Com amplitude de massa
unitária do carry (`‖u‖ = criticalAmplitude p k`), o resultante escalar é zero
(ângulo cego), a energia oculta é toda a energia, e essa energia vale
`2·criticalMass p k` — a **mesma** estrutura para qualquer base `p`. -/
theorem discrete_blindAngle_carry {p k : ℕ} (hp : 1 < p) (u : E)
    (hu : ‖u‖ = criticalAmplitude p k) :
    discreteResultant ![u, -u] = 0 ∧
      hiddenEnergy ![u, -u] = discreteEnergy ![u, -u] ∧
      discreteEnergy ![u, -u] = 2 * criticalMass p k ∧
      0 < discreteEnergy ![u, -u] := by
  have hres : discreteResultant ![u, -u] = 0 := by
    simp [discreteResultant, Fin.sum_univ_two]
  have henergy : discreteEnergy ![u, -u] = 2 * criticalMass p k := by
    rw [blindAngle_energy_eq_two_normSq, hu, criticalAmplitude_sq_eq_mass]
  refine ⟨hres, hiddenEnergy_eq_total_of_resultant_zero _ hres, henergy, ?_⟩
  rw [henergy]
  have hmass : 0 < criticalMass p k := by
    unfold criticalMass
    exact Real.rpow_pos_of_pos (by exact_mod_cast Nat.lt_of_lt_of_le one_pos hp.le) _
  linarith

end CPFormal.Analytic.Cp
