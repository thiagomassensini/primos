import Mathlib
import CPFormal.Analytic.CpBranchNorm

/-!
# Escala conforme radial e força restauradora do branch-norm

A lei dos 90° (`CpConformalJacobian`) mostra que o Jacobiano do plano de carry é
uma rotação de `90°` escalada por `k = |∂σ|`. Aqui identifica-se essa escala, no
nível da massa quadrática do ramo, com a derivada radial do `branchNormSq`:

`∂σ branchNormSq = -2 · branchConformalWeight`,

onde `branchConformalWeight` é o peso conforme (log-ponderado), estritamente
positivo. No eixo de equilíbrio `σ = 1/2` a forma fechada é exata:

`branchConformalWeight p (1/2) = p·log p / (p-1)`,   logo
`∂σ branchNormSq (1/2) = -2·p·log p/(p-1) ≠ 0`.

Isto é a **força restauradora** (numérica, §6) em forma fechada e puramente
geométrica: a saturação `branchNormSq = 1` em `σ = 1/2` tem inclinação radial
não nula na coordenada `criticalDisplacement = σ - 1/2`.

Genuine First: nenhum zeta, equação funcional ou RH é usado.
-/

namespace CPFormal.Analytic.Cp

open CPFormal.Carry.Cp

noncomputable section

/-- Peso conforme (log-ponderado) do ramo, forma fechada em `q = p^(-2σ)`. -/
def branchConformalWeight (p : ℕ) (sigma : ℝ) : ℝ :=
  ((p - 1 : ℕ) : ℝ) * Real.log p * branchRatio p sigma
    / (1 - branchRatio p sigma) ^ 2

/-- Derivada radial da razão quadrática `q(σ) = p^(-2σ)`. -/
theorem hasDerivAt_branchRatio (p : ℕ) (hp : Nat.Prime p) (sigma : ℝ) :
    HasDerivAt (fun σ : ℝ => branchRatio p σ)
      (-2 * Real.log p * branchRatio p sigma) sigma := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hin : HasDerivAt (fun x : ℝ => Real.log p * (-2 * x))
      (Real.log p * -2) sigma := by
    simpa using (((hasDerivAt_id sigma).const_mul (-2 : ℝ)).const_mul (Real.log p))
  have key : HasDerivAt (fun x : ℝ => Real.exp (Real.log p * (-2 * x)))
      (Real.exp (Real.log p * (-2 * sigma)) * (Real.log p * -2)) sigma :=
    (Real.hasDerivAt_exp _).comp sigma hin
  have hfun : (fun σ : ℝ => branchRatio p σ)
      = fun x : ℝ => Real.exp (Real.log p * (-2 * x)) := by
    funext x; rw [branchRatio, Real.rpow_def_of_pos hp0]
  rw [hfun]
  have hval : branchRatio p sigma = Real.exp (Real.log p * (-2 * sigma)) := by
    rw [branchRatio, Real.rpow_def_of_pos hp0]
  rw [hval]
  convert key using 1
  ring

/-- **Escala conforme = derivada radial da massa.** No semiplano de convergência,
`∂σ branchNormSq = -2 · branchConformalWeight`. -/
theorem hasDerivAt_branchNormSq (p : ℕ) (hp : Nat.Prime p) {sigma : ℝ}
    (hsigma : 0 < sigma) :
    HasDerivAt (fun σ : ℝ => branchNormSq p σ)
      (-2 * branchConformalWeight p sigma) sigma := by
  have hq := hasDerivAt_branchRatio p hp sigma
  have hlt := branchRatio_lt_one p hp hsigma
  have hne : (1 - branchRatio p sigma) ≠ 0 := by linarith
  have hsub : HasDerivAt (fun σ : ℝ => 1 - branchRatio p σ)
      (0 - (-2 * Real.log p * branchRatio p sigma)) sigma :=
    (hasDerivAt_const sigma (1 : ℝ)).sub hq
  have hinv := hsub.inv hne
  have hshift := hinv.sub_const (1 : ℝ)
  have hfull := hshift.const_mul (((p - 1 : ℕ) : ℝ))
  have heq : (fun σ : ℝ => branchNormSq p σ) =ᶠ[nhds sigma]
      fun σ : ℝ => ((p - 1 : ℕ) : ℝ) * ((1 - branchRatio p σ)⁻¹ - 1) := by
    filter_upwards [isOpen_Ioi.mem_nhds hsigma] with x hx
    have hdx : (1 - branchRatio p x) ≠ 0 := by
      have := branchRatio_lt_one p hp hx; linarith
    rw [branchNormSq_eq_closed p hp hx]; field_simp; ring
  have hbn := hfull.congr_of_eventuallyEq heq
  have hval :
      ((p - 1 : ℕ) : ℝ) *
        (-(0 - -2 * Real.log p * branchRatio p sigma)
          / (1 - branchRatio p sigma) ^ 2)
        = -2 * branchConformalWeight p sigma := by
    simp only [branchConformalWeight]
    field_simp
    ring
  rw [hval] at hbn
  exact hbn

/-- O peso conforme é estritamente positivo para uma base prima em `σ > 0`. -/
theorem branchConformalWeight_pos (p : ℕ) (hp : Nat.Prime p) {sigma : ℝ}
    (hsigma : 0 < sigma) : 0 < branchConformalWeight p sigma := by
  have hpos := branchRatio_pos p hp sigma
  have hlt := branchRatio_lt_one p hp hsigma
  have hne : (1 - branchRatio p sigma) ≠ 0 := by linarith
  have hlogpos : 0 < Real.log p := by
    have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    exact Real.log_pos h1
  have hpm1 : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    rw [Nat.cast_sub hp.one_le, Nat.cast_one]; linarith
  unfold branchConformalWeight
  positivity

/-- Forma fechada da escala conforme no eixo de equilíbrio `σ = 1/2`. -/
theorem branchConformalWeight_half (p : ℕ) (hp : Nat.Prime p) :
    branchConformalWeight p ((1 : ℝ) / 2)
      = (p : ℝ) * Real.log p / ((p : ℝ) - 1) := by
  unfold branchConformalWeight
  rw [branchRatio_half]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
  rw [Nat.cast_sub hp.one_le, Nat.cast_one]
  field_simp

/-- **Rigidez restauradora no eixo.** A derivada radial do `branchNormSq` em
`σ = 1/2` é `-2·p·log p/(p-1)`: a saturação unitária tem inclinação não nula na
coordenada `criticalDisplacement`. -/
theorem hasDerivAt_branchNormSq_half (p : ℕ) (hp : Nat.Prime p) :
    HasDerivAt (fun σ : ℝ => branchNormSq p σ)
      (-2 * ((p : ℝ) * Real.log p / ((p : ℝ) - 1))) ((1 : ℝ) / 2) := by
  have h := hasDerivAt_branchNormSq p hp (sigma := (1 : ℝ) / 2) (by norm_num)
  rwa [branchConformalWeight_half p hp] at h

/-- A inclinação restauradora no eixo é estritamente negativa. -/
theorem branchNormSq_deriv_half_neg (p : ℕ) (hp : Nat.Prime p) :
    -2 * ((p : ℝ) * Real.log p / ((p : ℝ) - 1)) < 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlogpos : 0 < Real.log p := Real.log_pos hp1
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hfrac : 0 < (p : ℝ) * Real.log p / ((p : ℝ) - 1) := by positivity
  linarith

end

end CPFormal.Analytic.Cp
