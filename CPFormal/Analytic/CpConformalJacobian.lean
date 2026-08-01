import Mathlib
import CPFormal.Analytic.CpReflectedEndpoint

/-!
# Identidade conforme do plano de carry (lei dos 90 graus)

No plano real de amplitude+fase `ℂ`, o gradiente radial `∂σ` e o de fase `∂t`
do estado/ressonância são sempre ortogonais e de igual magnitude: o Jacobiano é
uma rotação de `90°` escalada. Como `Rot(90°)` é a multiplicação por
`Complex.I`, a lei é

`∂t f(σ + t·I) = I · ∂σ f(σ + t·I)`

para qualquer `f` complexo-diferenciável (Cauchy–Riemann). Este módulo sela a
lei geral, seus corolários métricos (mesma norma; ortogonalidade), e a
instância no termo de Dirichlet `positiveDirichletValue` usado pelas cartas.

Genuine First: nenhum zeta, equação funcional ou RH é usado.
-/

namespace CPFormal.Analytic.Cp

open Complex

noncomputable section

/-- Derivada radial de `f` ao longo de `ς ↦ ς + t·I`: vale `f'`. -/
theorem hasDerivAt_conformal_sigma {f : ℂ → ℂ} {f' : ℂ} {σ t : ℝ}
    (h : HasDerivAt f f' ((σ : ℂ) + (t : ℂ) * I)) :
    HasDerivAt (fun ς : ℝ => f ((ς : ℂ) + (t : ℂ) * I)) f' σ := by
  have hg : HasDerivAt (fun z : ℂ => z + (t : ℂ) * I) 1 (σ : ℂ) := by
    simpa using (hasDerivAt_id (σ : ℂ)).add_const ((t : ℂ) * I)
  have hcomp : HasDerivAt (fun y : ℝ => f ((y : ℂ) + (t : ℂ) * I)) (f' * 1) σ :=
    (h.comp (σ : ℂ) hg).comp_ofReal
  simpa using hcomp

/-- Derivada de fase de `f` ao longo de `τ ↦ σ + τ·I`: vale `I · f'`. -/
theorem hasDerivAt_conformal_t {f : ℂ → ℂ} {f' : ℂ} {σ t : ℝ}
    (h : HasDerivAt f f' ((σ : ℂ) + (t : ℂ) * I)) :
    HasDerivAt (fun τ : ℝ => f ((σ : ℂ) + (τ : ℂ) * I)) (I * f') t := by
  have hg : HasDerivAt (fun z : ℂ => (σ : ℂ) + z * I) I (t : ℂ) := by
    have hbase := (hasDerivAt_id (t : ℂ)).mul_const I
    simpa using hbase.const_add (σ : ℂ)
  have hcomp : HasDerivAt (fun y : ℝ => f ((σ : ℂ) + (y : ℂ) * I)) (f' * I) t :=
    (h.comp (t : ℂ) hg).comp_ofReal
  rw [mul_comm]
  exact hcomp

/-- **Lei dos 90 graus.** Para `f` complexo-diferenciável, a derivada de fase é
`I` (rotação de `90°`) vezes a derivada radial. -/
theorem conformal_deriv_t_eq_I_mul_deriv_sigma {f : ℂ → ℂ} {f' : ℂ} {σ t : ℝ}
    (h : HasDerivAt f f' ((σ : ℂ) + (t : ℂ) * I)) :
    deriv (fun τ : ℝ => f ((σ : ℂ) + (τ : ℂ) * I)) t
      = I * deriv (fun ς : ℝ => f ((ς : ℂ) + (t : ℂ) * I)) σ := by
  rw [(hasDerivAt_conformal_t h).deriv, (hasDerivAt_conformal_sigma h).deriv]

/-- Corolário métrico 1: a rotação de `90°` preserva a norma, logo
`‖∂t‖ = ‖∂σ‖`. -/
theorem conformal_norm_eq (f' : ℂ) : ‖I * f'‖ = ‖f'‖ := by
  rw [norm_mul, Complex.norm_I, one_mul]

/-- Corolário métrico 2: gradiente radial e de fase são ortogonais — a parte
real do pareamento `conj(∂σ) · ∂t` é zero. -/
theorem conformal_orthogonal (f' : ℂ) :
    ((starRingEnd ℂ) f' * (I * f')).re = 0 := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.I_re, Complex.I_im]
  ring

/-- O termo de Dirichlet `z ↦ (n+1)^(-z)` é complexo-diferenciável. -/
theorem differentiableAt_positiveDirichletValue (s : ℂ) (n : ℕ) :
    DifferentiableAt ℂ (fun z : ℂ => positiveDirichletValue z n) s := by
  have hc : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hrewrite :
      (fun z : ℂ => positiveDirichletValue z n)
        = fun z : ℂ => Complex.exp (Complex.log ((n + 1 : ℕ) : ℂ) * (-z)) := by
    funext z
    rw [positiveDirichletValue, Complex.cpow_def_of_ne_zero hc]
  rw [hrewrite]
  have hinner :
      DifferentiableAt ℂ
        (fun z : ℂ => Complex.log ((n + 1 : ℕ) : ℂ) * (-z)) s :=
    ((differentiableAt_id).neg).const_mul (Complex.log ((n + 1 : ℕ) : ℂ))
  exact DifferentiableAt.comp s Complex.differentiable_exp.differentiableAt hinner

/-- A lei dos 90 graus aplicada ao termo de Dirichlet do operador: na carta real
de fase, `∂t` é `I` vezes `∂σ`. -/
theorem conformal_positiveDirichletValue (n : ℕ) (σ t : ℝ) :
    deriv (fun τ : ℝ => positiveDirichletValue ((σ : ℂ) + (τ : ℂ) * I) n) t
      = I *
        deriv (fun ς : ℝ => positiveDirichletValue ((ς : ℂ) + (t : ℂ) * I) n) σ :=
  conformal_deriv_t_eq_I_mul_deriv_sigma
    ((differentiableAt_positiveDirichletValue ((σ : ℂ) + (t : ℂ) * I) n).hasDerivAt)

end

end CPFormal.Analytic.Cp
