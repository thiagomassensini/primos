import CPFormal.Analytic.CpNativeCarryLogPhaseOrbit

/-!
# The native log-jet is the logarithmic generator channel

The log-weighted Dirichlet field was defined independently as

`positiveLogDirichletValue s n = log(n+1) * positiveDirichletValue s n`.

The finite real-spectral generator was also defined independently as the
self-adjoint diagonal multiplier

`L_N x(n) = log(n+1) * x(n)`.

This module proves that these two constructions are literally the same channel
on the native real-spectral state:

`LogJet_N(t) = L_N psi_N(t)`.

It also proves that the generator commutes with the unitary log-phase evolution,
so the log-jet itself is the orbit of the fixed seed `LogJet_N(0)`.  No zero,
resonance, bracket closure, or boundary hypothesis is used.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-- The finite log-jet vector on the native real-spectral orbit. -/
def finiteRealSpectralLogJetVector (N : ℕ) (t : ℝ) :
    FiniteRealSpectralHilbert N :=
  WithLp.toLp 2 fun n =>
    positiveLogDirichletValue (criticalLineParameter t) n.1

@[simp] theorem finiteRealSpectralLogJetVector_apply
    (N : ℕ) (t : ℝ) (n : Fin N) :
    finiteRealSpectralLogJetVector N t n =
      positiveLogDirichletValue (criticalLineParameter t) n.1 := rfl

/-- The independently defined log-jet is exactly the logarithmic generator
applied to the same native state. -/
theorem finiteRealSpectralLogJetVector_eq_generator_state
    (N : ℕ) (t : ℝ) :
    finiteRealSpectralLogJetVector N t =
      finiteRealSpectralGenerator N (finiteRealSpectralStateVector N t) := by
  ext n
  rw [finiteRealSpectralLogJetVector_apply,
    finiteRealSpectralGenerator_apply,
    finiteRealSpectralStateVector_apply]
  rfl

/-- The finite logarithmic generator commutes exactly with its diagonal unitary
evolution. -/
theorem finiteRealSpectralGenerator_evolution_commute
    (N : ℕ) (t : ℝ) (x : FiniteRealSpectralHilbert N) :
    finiteRealSpectralGenerator N (finiteRealSpectralEvolution N t x) =
      finiteRealSpectralEvolution N t (finiteRealSpectralGenerator N x) := by
  ext n
  rw [finiteRealSpectralGenerator_apply,
    finiteRealSpectralEvolution_apply,
    finiteRealSpectralEvolution_apply,
    finiteRealSpectralGenerator_apply]
  ring

/-- The native log-jet is itself the unitary orbit of the fixed log-jet seed at
time zero. -/
theorem finiteRealSpectralLogJetVector_eq_evolution_zero
    (N : ℕ) (t : ℝ) :
    finiteRealSpectralLogJetVector N t =
      finiteRealSpectralEvolution N t
        (finiteRealSpectralLogJetVector N 0) := by
  calc
    finiteRealSpectralLogJetVector N t =
        finiteRealSpectralGenerator N (finiteRealSpectralStateVector N t) :=
      finiteRealSpectralLogJetVector_eq_generator_state N t
    _ = finiteRealSpectralGenerator N
          (finiteRealSpectralEvolution N t
            (finiteRealSpectralStateVector N 0)) := by
      rw [finiteRealSpectralStateVector_eq_evolution_zero]
    _ = finiteRealSpectralEvolution N t
          (finiteRealSpectralGenerator N
            (finiteRealSpectralStateVector N 0)) :=
      finiteRealSpectralGenerator_evolution_commute N t _
    _ = finiteRealSpectralEvolution N t
          (finiteRealSpectralLogJetVector N 0) := by
      rw [← finiteRealSpectralLogJetVector_eq_generator_state]

/-- The log-jet norm is constant along real time for the same unitary reason as
the state norm. -/
theorem finiteRealSpectralLogJetVector_norm_eq_zero
    (N : ℕ) (t : ℝ) :
    ‖finiteRealSpectralLogJetVector N t‖ =
      ‖finiteRealSpectralLogJetVector N 0‖ := by
  rw [finiteRealSpectralLogJetVector_eq_evolution_zero]
  exact (finiteRealSpectralEvolution N t).norm_map _

end

end CPFormal.Analytic.Cp
