import CPFormal.Analytic.CpInfiniteRealSpectralGenerator
import CPFormal.Analytic.CpNativeCarrySymmetricBoundaryCondition

/-!
# Native carry state as the logarithmic unitary orbit

The real-spectral state was originally written in Dirichlet notation,

`psi_t(n) = (n+1)^(-(1/2 + t I))`.

The self-adjoint logarithmic generator was constructed independently and its
unitary group acts coordinatewise by

`U_t x(n) = exp(-t log(n+1) I) x(n)`.

This module proves that these are literally the same state:

`psi_t = U_t psi_0`.

The result is first proved coordinatewise and then on every finite Hilbert
cutoff.  No resonance, zero, boundary condition, or scalar Genuine identity is
used.  It fixes the role of `t` before the remaining boundary linearization:
`t` is the real time of the log-phase group, while the critical amplitude is
contained entirely in the seed `psi_0`.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Coordinatewise factorization of the real-spectral state into the critical
seed amplitude and the unitary logarithmic phase. -/
theorem realSpectralState_eq_logPhase_mul_zero
    (t : ℝ) (n : ℕ) :
    realSpectralState t n =
      infiniteRealSpectralPhase t n * realSpectralState 0 n := by
  let x : ℝ := ((n + 1 : ℕ) : ℝ)
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  unfold realSpectralState positiveDirichletValue criticalLineParameter
    infiniteRealSpectralPhase infiniteRealSpectralFrequency
  change
    (x : ℂ) ^
        (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
      Complex.exp
          (-(((t * Real.log x : ℝ) : ℂ) * Complex.I)) *
        (x : ℂ) ^
          (-(((1 / 2 : ℝ) : ℂ) + (0 : ℂ) * Complex.I))
  rw [Complex.cpow_def_of_ne_zero hxC,
    Complex.cpow_def_of_ne_zero hxC, ← Complex.exp_add]
  rw [← Complex.ofReal_log hx.le]
  congr 1
  push_cast
  ring

/-- The finite and infinite phase notations agree on a finite coordinate. -/
@[simp] theorem finiteRealSpectralPhase_eq_infinite
    {N : ℕ} (t : ℝ) (n : Fin N) :
    finiteRealSpectralPhase t n = infiniteRealSpectralPhase t n.1 := by
  rfl

/-- At every finite cutoff, the previously defined real-spectral vector is
exactly the unitary orbit of its critical seed at time zero. -/
theorem finiteRealSpectralStateVector_eq_evolution_zero
    (N : ℕ) (t : ℝ) :
    finiteRealSpectralStateVector N t =
      finiteRealSpectralEvolution N t
        (finiteRealSpectralStateVector N 0) := by
  ext n
  rw [finiteRealSpectralStateVector_apply,
    finiteRealSpectralEvolution_apply,
    finiteRealSpectralStateVector_apply,
    finiteRealSpectralPhase_eq_infinite]
  exact realSpectralState_eq_logPhase_mul_zero t n.1

/-- The finite real-spectral orbit has constant norm because it is the orbit of
one fixed seed under the unitary logarithmic evolution. -/
theorem finiteRealSpectralStateVector_norm_eq_zero
    (N : ℕ) (t : ℝ) :
    ‖finiteRealSpectralStateVector N t‖ =
      ‖finiteRealSpectralStateVector N 0‖ := by
  rw [finiteRealSpectralStateVector_eq_evolution_zero]
  exact (finiteRealSpectralEvolution N t).norm_map _

end

end CPFormal.Analytic.Cp
