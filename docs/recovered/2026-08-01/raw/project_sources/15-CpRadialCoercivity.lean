import Mathlib
import CPFormal.Analytic.CpFiniteGreenRadial

/-!
# Coercividade radial (o núcleo do intertwiner)

A rigidez conforme (`CpConformalBranchScale`) mostra que a escala radial satura
em `log p` no eixo. Aqui prova-se a versão **quantitativa e global**: o cofator
radial nunca fica abaixo de `log p`, logo o desequilíbrio radial é limitado por
baixo linearmente no deslocamento crítico:

`log p ≤ cpRadialCofactor p δ`,   e portanto
`2·|δ|·log p ≤ |cpRadialDifference p δ|`.

Esta é a coercividade que um "intertwiner coercivo" exige: a parte radial do
pareamento de Green refletido só pode se anular em `δ = 0`, e o faz com taxa
mínima conhecida. Nenhum zero Genuine é assumido; nenhuma ponte é declarada.

Genuine First: nenhum zeta, equação funcional ou RH é usado.
-/

namespace CPFormal.Analytic.Cp

open CPFormal.Carry.Cp

noncomputable section

/-- Derivada radial de `y ↦ p^y`. -/
theorem hasDerivAt_rpow_id (p : ℕ) (hp0 : 0 < (p : ℝ)) (δ : ℝ) :
    HasDerivAt (fun y : ℝ => (p : ℝ) ^ y) (Real.log p * (p : ℝ) ^ δ) δ := by
  have hfun : (fun y : ℝ => (p : ℝ) ^ y)
      = fun y : ℝ => Real.exp (Real.log p * y) := by
    funext y; rw [Real.rpow_def_of_pos hp0]
  have hval : Real.log p * (p : ℝ) ^ δ
      = Real.exp (Real.log p * δ) * Real.log p := by
    rw [Real.rpow_def_of_pos hp0]; ring
  rw [hfun, hval]
  have hin : HasDerivAt (fun y : ℝ => Real.log p * y) (Real.log p) δ := by
    simpa using (hasDerivAt_id δ).const_mul (Real.log p)
  exact (Real.hasDerivAt_exp _).comp δ hin

/-- Derivada radial de `y ↦ p^(-y)`. -/
theorem hasDerivAt_rpow_neg (p : ℕ) (hp0 : 0 < (p : ℝ)) (δ : ℝ) :
    HasDerivAt (fun y : ℝ => (p : ℝ) ^ (-y))
      (-(Real.log p) * (p : ℝ) ^ (-δ)) δ := by
  have hfun : (fun y : ℝ => (p : ℝ) ^ (-y))
      = fun y : ℝ => Real.exp (Real.log p * (-y)) := by
    funext y; rw [Real.rpow_def_of_pos hp0]
  have hval : -(Real.log p) * (p : ℝ) ^ (-δ)
      = Real.exp (Real.log p * (-δ)) * (Real.log p * -1) := by
    rw [Real.rpow_def_of_pos hp0]; ring
  rw [hfun, hval]
  have hin : HasDerivAt (fun y : ℝ => Real.log p * (-y)) (Real.log p * -1) δ :=
    ((hasDerivAt_id δ).neg).const_mul (Real.log p)
  exact (Real.hasDerivAt_exp _).comp δ hin

/-- O "gap" radial `p^δ - p^(-δ) - 2δ log p`. -/
def radialGap (p : ℕ) (delta : ℝ) : ℝ :=
  cpRadialDifference p delta - 2 * delta * Real.log p

theorem hasDerivAt_radialGap (p : ℕ) (hp0 : 0 < (p : ℝ)) (δ : ℝ) :
    HasDerivAt (fun x : ℝ => radialGap p x)
      (Real.log p * ((p : ℝ) ^ δ + (p : ℝ) ^ (-δ) - 2)) δ := by
  have h1 := hasDerivAt_rpow_id p hp0 δ
  have h2 := hasDerivAt_rpow_neg p hp0 δ
  have hlin : HasDerivAt (fun x : ℝ => 2 * x * Real.log p) (2 * Real.log p) δ := by
    simpa [mul_comm, mul_assoc] using
      (((hasDerivAt_id δ).const_mul (2 : ℝ)).mul_const (Real.log p))
  have hval : Real.log p * ((p : ℝ) ^ δ + (p : ℝ) ^ (-δ) - 2)
      = Real.log p * (p : ℝ) ^ δ - -(Real.log p) * (p : ℝ) ^ (-δ)
          - 2 * Real.log p := by ring
  have hfun : (fun x : ℝ => radialGap p x)
      = fun x : ℝ => ((p : ℝ) ^ x - (p : ℝ) ^ (-x)) - 2 * x * Real.log p := by
    funext x; rfl
  rw [hval, hfun]
  exact (h1.sub h2).sub hlin

/-- A derivada do gap radial é não negativa (AM–GM: `p^δ + p^(-δ) ≥ 2`). -/
theorem radialGap_deriv_nonneg (p : ℕ) (hp : Nat.Prime p) (δ : ℝ) :
    0 ≤ Real.log p * ((p : ℝ) ^ δ + (p : ℝ) ^ (-δ) - 2) := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hlog : 0 ≤ Real.log p :=
    Real.log_nonneg (by exact_mod_cast hp.one_le)
  have ha : 0 < (p : ℝ) ^ δ := Real.rpow_pos_of_pos hp0 δ
  have hinv : (p : ℝ) ^ (-δ) = ((p : ℝ) ^ δ)⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hp0)]
  have hane : (p : ℝ) ^ δ ≠ 0 := ne_of_gt ha
  have hmulinv : (p : ℝ) ^ δ * ((p : ℝ) ^ δ)⁻¹ = 1 := mul_inv_cancel₀ hane
  have ham : (2 : ℝ) ≤ (p : ℝ) ^ δ + (p : ℝ) ^ (-δ) := by
    rw [hinv]
    nlinarith [sq_nonneg ((p : ℝ) ^ δ - 1), ha, hmulinv]
  have hfac : 0 ≤ (p : ℝ) ^ δ + (p : ℝ) ^ (-δ) - 2 := by linarith
  exact mul_nonneg hlog hfac

/-- `radialGap` é monótono (não decrescente) em todo `ℝ`. -/
theorem radialGap_monotone (p : ℕ) (hp : Nat.Prime p) :
    Monotone (fun δ : ℝ => radialGap p δ) := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  refine monotone_of_deriv_nonneg ?_ ?_
  · exact fun x => (hasDerivAt_radialGap p hp0 x).differentiableAt
  · intro x
    rw [(hasDerivAt_radialGap p hp0 x).deriv]
    exact radialGap_deriv_nonneg p hp x

@[simp] theorem radialGap_zero (p : ℕ) : radialGap p 0 = 0 := by
  simp [radialGap, cpRadialDifference, neg_zero, Real.rpow_zero]

/-- **Coercividade radial.** O cofator radial nunca fica abaixo de `log p`. -/
theorem cpRadialCofactor_ge_log (p : ℕ) (hp : Nat.Prime p) (δ : ℝ) :
    Real.log p ≤ cpRadialCofactor p δ := by
  rcases eq_or_ne δ 0 with h0 | h0
  · subst δ; simp [cpRadialCofactor]
  · rw [cpRadialCofactor, if_neg h0]
    have hmono := radialGap_monotone p hp
    have hne2 : (2 : ℝ) * δ ≠ 0 := mul_ne_zero (by norm_num) h0
    have hkey : cpRadialDifference p δ / (2 * δ)
        = Real.log p + radialGap p δ / (2 * δ) := by
      rw [radialGap]
      field_simp
      ring
    rw [hkey]
    have hnn : 0 ≤ radialGap p δ / (2 * δ) := by
      rcases lt_or_gt_of_ne h0 with hneg | hpos
      · have hle : radialGap p δ ≤ 0 := by
          have := hmono (le_of_lt hneg); simpa using this
        have h2 : 2 * δ < 0 := by linarith
        rw [← neg_div_neg_eq]
        exact div_nonneg (by linarith) (by linarith)
      · have hge : 0 ≤ radialGap p δ := by
          have := hmono (le_of_lt hpos); simpa using this
        have h2 : 0 < 2 * δ := by linarith
        exact div_nonneg hge (le_of_lt h2)
    linarith

/-- **Coercividade do desequilíbrio radial.** O módulo do defeito radial é
limitado por baixo por `2|δ|·log p`. -/
theorem abs_cpRadialDifference_ge (p : ℕ) (hp : Nat.Prime p) (δ : ℝ) :
    2 * |δ| * Real.log p ≤ |cpRadialDifference p δ| := by
  have hcof := cpRadialCofactor_ge_log p hp δ
  have hcofpos := cpRadialCofactor_pos p hp δ
  have h2δ : (0 : ℝ) ≤ 2 * |δ| := by positivity
  rw [cpRadialDifference_eq_two_mul_delta_mul_cofactor p δ,
    abs_mul, abs_mul, abs_two, abs_of_pos hcofpos]
  exact mul_le_mul_of_nonneg_left hcof h2δ

end

end CPFormal.Analytic.Cp
