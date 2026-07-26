import CPFormal.Analytic.CpNativeCarryWeightedSpectralState
import Mathlib.Analysis.PSeries

/-!
# Harmonic threshold of the native carry spectrum

The native critical state has coordinate norm `(n+1)^(-1/2)`.  Squaring the
amplitude therefore gives exactly the harmonic mass `(n+1)^(-1)`.  The Lean
kernel proves that the sum of these quadratic masses is not summable.

Consequently the undamped critical orbit is a generalized/continuous spectral
state rather than an ordinary `ell^2` eigenvector.  The additional vertical
factor `q^n`, `0 <= q < 1`, places the state in the carry Hilbert space, but that
is a genuine radial dressing and must not be silently identified with the
undamped spectral vector.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-- The quadratic mass of one critical real-spectral coordinate is exactly the
shifted harmonic weight. -/
theorem norm_realSpectralState_sq_eq_inv
    (t : ℝ) (n : ℕ) :
    ‖realSpectralState t n‖ ^ 2 =
      (((n + 1 : ℕ) : ℝ))⁻¹ := by
  rw [norm_realSpectralState]
  have hbase : 0 ≤ (((n + 1 : ℕ) : ℝ)) := by positivity
  calc
    ((((n + 1 : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))) ^ 2 =
        (((n + 1 : ℕ) : ℝ)) ^
          ((-(1 / 2 : ℝ)) * (2 : ℝ)) := by
      exact
        (Real.rpow_mul_natCast hbase (-(1 / 2 : ℝ)) 2).symm
    _ = (((n + 1 : ℕ) : ℝ)) ^ (-1 : ℝ) := by
      congr 1
      ring
    _ = (((n + 1 : ℕ) : ℝ))⁻¹ := by
      simpa using
        (Real.rpow_neg hbase (1 : ℝ))

/-- The quadratic masses of the undamped native critical orbit form the
harmonic series and are not summable. -/
theorem not_summable_norm_sq_realSpectralState (t : ℝ) :
    ¬ Summable (fun n : ℕ => ‖realSpectralState t n‖ ^ 2) := by
  intro hs
  have hharmonic :
      Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹) :=
    hs.congr (fun n => norm_realSpectralState_sq_eq_inv t n)
  have horiginal :
      Summable (fun n : ℕ => ((n : ℝ))⁻¹) := by
    apply (_root_.summable_nat_add_iff 1).1
    simpa using hharmonic
  exact Real.not_summable_natCast_inv horiginal

/-- Named statement: the native critical orbit is at the continuous-spectrum
threshold, independently of the real phase time. -/
def NativeCarryCriticalOrbitIsGeneralized : Prop :=
  ∀ t : ℝ, ¬ Summable (fun n : ℕ => ‖realSpectralState t n‖ ^ 2)

/-- The preceding threshold statement holds for the full native real orbit. -/
theorem nativeCarryCriticalOrbitIsGeneralized :
    NativeCarryCriticalOrbitIsGeneralized :=
  not_summable_norm_sq_realSpectralState

end

end CPFormal.Analytic.Cp
