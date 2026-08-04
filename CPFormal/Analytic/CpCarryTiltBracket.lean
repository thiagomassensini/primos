import CPFormal.Analytic.CpBranchNorm
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Tilt de carry: o sinal da curvatura do peso e a seleção nativa de 1/2

Completa a linha nativa que nasce do carry — massa, operador de ramo, amplitude,
norma quadrática, bracket — com o **tilt**: a segunda diferença centrada do peso
inclinado `x^(-δ)` sobre um centro `c`.

* `carryBracket2 f c = f(c-1) + f(c+1) - 2 f(c)` — segunda diferença centrada;
* `carryTilt δ x = x^(-δ)` — o peso inclinado por `δ`;
* `carryTiltBracket δ c = carryBracket2 (carryTilt δ) c` — a curvatura do peso.

O núcleo é puramente de convexidade: para `c > 1`,

* `δ = 0`  ⟹ curvatura nula;
* `δ > 0`  ⟹ curvatura estritamente positiva (peso estritamente convexo);
* `-1 < δ < 0` ⟹ curvatura estritamente negativa (peso estritamente côncavo).

Logo `carryTiltBracket δ c = 0 ↔ δ = 0`.  Com `δ = criticalDisplacement σ =
σ - 1/2`, a curvatura do peso zera **exatamente** em `σ = 1/2`, e seu sinal é o
sinal de `σ - 1/2`.  É a seleção do expoente autodual pela curvatura do carry,
sem equação funcional, sem reflexão `σ ↦ 1-σ`, sem zeta.

Genuine First: nenhum zeta, equação funcional, número imaginário ou RH.
-/

open scoped BigOperators

namespace CPFormal.Analytic.Cp

open CPFormal.Carry.Cp

noncomputable section

/-- Segunda diferença centrada de `f` no centro `c`. -/
def carryBracket2 (f : ℝ → ℝ) (c : ℝ) : ℝ :=
  f (c - 1) + f (c + 1) - 2 * f c

/-- Peso de carry inclinado por `δ`: `x ↦ x^(-δ)`. -/
def carryTilt (δ x : ℝ) : ℝ :=
  x ^ (-δ)

/-- Curvatura do peso inclinado: a segunda diferença de `x^(-δ)` no centro `c`. -/
def carryTiltBracket (δ c : ℝ) : ℝ :=
  carryBracket2 (carryTilt δ) c

@[simp] theorem carryTiltBracket_zero (c : ℝ) :
    carryTiltBracket 0 c = 0 := by
  unfold carryTiltBracket carryBracket2 carryTilt
  simp only [neg_zero, Real.rpow_zero]
  ring

/-- A segunda diferença centrada de uma função estritamente convexa em `Ioi 0`
é positiva quando `c > 1`. -/
theorem carryCenteredSecond_pos_of_strictConvexOn_Ioi {f : ℝ → ℝ}
    (hconv : StrictConvexOn ℝ (Set.Ioi 0) f) {c : ℝ} (hc : 1 < c) :
    0 < f (c - 1) + f (c + 1) - 2 * f c := by
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  have hcm1 : c - 1 ∈ Set.Ioi 0 := sub_pos.mpr hc
  have hcp1 : c + 1 ∈ Set.Ioi 0 := add_pos hc0 zero_lt_one
  have hxy : c - 1 ≠ c + 1 := by linarith
  have hmid := hconv.2 hcm1 hcp1 hxy (by norm_num : 0 < (1 / 2 : ℝ))
    (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hcomb : (2 : ℝ)⁻¹ * (c - 1) + (2 : ℝ)⁻¹ * (c + 1) = c := by ring
  have hmid1 :
      f c < (2 : ℝ)⁻¹ * f (c - 1) + (2 : ℝ)⁻¹ * f (c + 1) := by
    simpa [hcomb, smul_eq_mul] using hmid
  nlinarith [hmid1]

/-- A segunda diferença centrada de uma função estritamente côncava em `Ici 0`
é negativa quando `c > 1`. -/
theorem carryCenteredSecond_neg_of_strictConcaveOn_Ici {f : ℝ → ℝ}
    (hconc : StrictConcaveOn ℝ (Set.Ici 0) f) {c : ℝ} (hc : 1 < c) :
    f (c - 1) + f (c + 1) - 2 * f c < 0 := by
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  have hcm1 : c - 1 ∈ Set.Ici 0 := sub_nonneg.mpr (le_of_lt hc)
  have hcp1 : c + 1 ∈ Set.Ici 0 := le_of_lt (add_pos hc0 zero_lt_one)
  have hxy : c - 1 ≠ c + 1 := by linarith
  have hmid := hconc.2 hcm1 hcp1 hxy (by norm_num : 0 < (1 / 2 : ℝ))
    (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hcomb : (2 : ℝ)⁻¹ * (c - 1) + (2 : ℝ)⁻¹ * (c + 1) = c := by ring
  have hmid1 :
      (2 : ℝ)⁻¹ * f (c - 1) + (2 : ℝ)⁻¹ * f (c + 1) < f c := by
    simpa [hcomb, smul_eq_mul] using hmid
  nlinarith [hmid1]

/-- Para `p < 0`, `x ↦ x^p` é estritamente convexa em `(0, ∞)`. -/
theorem strictConvexOn_rpow_of_neg {p : ℝ} (hp : p < 0) :
    StrictConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => x ^ p) := by
  apply strictConvexOn_of_deriv2_pos' (convex_Ioi 0)
  · exact fun x hx =>
      (Real.continuousAt_rpow_const x p (Or.inl (ne_of_gt hx))).continuousWithinAt
  intro x hx
  rw [Set.mem_Ioi] at hx
  simp only [Real.iter_deriv_rpow_const]
  apply mul_pos
  · have hpoch : (descPochhammer ℝ 2).eval p = p * (p - 1) := by
      simp [descPochhammer, Polynomial.eval_mul, Polynomial.eval_sub]
    rw [hpoch]
    exact mul_pos_of_neg_of_neg hp (by linarith)
  · exact Real.rpow_pos_of_pos hx _

/-- Curvatura positiva acima do autodual: `δ > 0` ⟹ peso estritamente convexo. -/
theorem carryTiltBracket_pos_of_pos {δ c : ℝ} (hδ : 0 < δ) (hc : 1 < c) :
    0 < carryTiltBracket δ c := by
  have hp : -δ < 0 := by linarith
  have hconv := strictConvexOn_rpow_of_neg hp
  have hpos := carryCenteredSecond_pos_of_strictConvexOn_Ioi hconv hc
  simpa [carryTiltBracket, carryBracket2, carryTilt] using hpos

/-- Curvatura negativa abaixo do autodual: `-1 < δ < 0` ⟹ peso estritamente
côncavo. -/
theorem carryTiltBracket_neg_of_neg_one_lt {δ c : ℝ}
    (hδ0 : -1 < δ) (hδ1 : δ < 0) (hc : 1 < c) :
    carryTiltBracket δ c < 0 := by
  have hp0 : 0 < -δ := by linarith
  have hp1 : -δ < 1 := by linarith
  have hconc : StrictConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ (-δ)) :=
    Real.strictConcaveOn_rpow hp0 hp1
  have hneg := carryCenteredSecond_neg_of_strictConcaveOn_Ici hconc hc
  simpa [carryTiltBracket, carryBracket2, carryTilt] using hneg

/-- **Rigidez da curvatura do carry.**  Para `c > 1` e `δ > -1`, a curvatura do
peso inclinado anula-se exatamente no expoente autodual `δ = 0`. -/
theorem carryTiltBracket_eq_zero_iff {δ c : ℝ}
    (hδ : -1 < δ) (hc : 1 < c) :
    carryTiltBracket δ c = 0 ↔ δ = 0 := by
  constructor
  · intro hzero
    rcases lt_trichotomy δ 0 with hneg | h0 | hpos
    · exact absurd hzero (ne_of_lt
        (carryTiltBracket_neg_of_neg_one_lt hδ hneg hc))
    · exact h0
    · exact absurd hzero (ne_of_gt (carryTiltBracket_pos_of_pos hpos hc))
  · intro h0
    rw [h0, carryTiltBracket_zero]

/-! ## Ponte com a coordenada transversal `criticalDisplacement` -/

/-- Com `δ = σ - 1/2`, a curvatura do peso zera exatamente em `σ = 1/2`. -/
theorem carryTiltBracket_criticalDisplacement_eq_zero_iff
    {sigma c : ℝ} (hsigma : 0 < sigma) (hc : 1 < c) :
    carryTiltBracket (criticalDisplacement sigma) c = 0 ↔ sigma = (1 : ℝ) / 2 := by
  have hδ : -1 < criticalDisplacement sigma := by
    unfold criticalDisplacement; linarith
  rw [carryTiltBracket_eq_zero_iff hδ hc]
  unfold criticalDisplacement
  constructor <;> intro h <;> linarith

/-- Acima da linha crítica a curvatura é estritamente positiva. -/
theorem carryTiltBracket_criticalDisplacement_pos_of_half_lt
    {sigma c : ℝ} (hsigma : (1 : ℝ) / 2 < sigma) (hc : 1 < c) :
    0 < carryTiltBracket (criticalDisplacement sigma) c := by
  apply carryTiltBracket_pos_of_pos _ hc
  unfold criticalDisplacement; linarith

/-- Abaixo da linha crítica (mas ainda `σ > -1/2`) a curvatura é estritamente
negativa. -/
theorem carryTiltBracket_criticalDisplacement_neg_of_lt_half
    {sigma c : ℝ} (hsigma0 : -(1 : ℝ) / 2 < sigma)
    (hsigma : sigma < (1 : ℝ) / 2) (hc : 1 < c) :
    carryTiltBracket (criticalDisplacement sigma) c < 0 := by
  apply carryTiltBracket_neg_of_neg_one_lt _ _ hc <;>
    unfold criticalDisplacement <;> linarith

/-- **Não-anulação off-critical nativa.**  Fora do autodual `σ = 1/2` (com
`σ > 0`, `c > 1`), a curvatura do peso de carry é estritamente diferente de
zero — direto do sinal, sem reflexão nem equação funcional. -/
theorem carryTiltBracket_criticalDisplacement_ne_zero_of_ne_half
    {sigma c : ℝ} (hsigma : 0 < sigma) (hc : 1 < c)
    (hhalf : sigma ≠ (1 : ℝ) / 2) :
    carryTiltBracket (criticalDisplacement sigma) c ≠ 0 := by
  rw [Ne, carryTiltBracket_criticalDisplacement_eq_zero_iff hsigma hc]
  exact hhalf

end

end CPFormal.Analytic.Cp
