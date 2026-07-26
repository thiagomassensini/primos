import CPFormal.Analytic.CpNativeCarryLogJetGenerator
import CPFormal.Analytic.CpCarryWeightedVerticalReturn

/-!
# Infinite weighted native spectral state in the vertical carry Hilbert space

The vertical valve acts on amplitude coordinates.  Its native spectral input is
therefore the real-spectral orbit dressed by the vertical carry ratio:

`x_(q,t)(n) = q^n * psi_t(n)`.

For `0 <= q < 1`, the geometric amplitude vector `q^n` is already in `ell^2`.
The critical state satisfies `||psi_t(n)|| <= 1`, so the dressed state belongs to
the same Hilbert space by direct domination.  No cutoff, zero, resonance or
boundary condition is used.

The module then computes the native initial trace exactly and proves that the
dressed centered bracket is just the ordinary centered second difference of the
undressed spectral state, multiplied by the common carry amplitude `q^(n+1)`.
This is the cutoff-free state on which the distinguished boundary condition must
act.
-/

open scoped lp ENNReal NNReal

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Every critical real-spectral coordinate has norm at most one. -/
theorem norm_realSpectralState_le_one (t : ℝ) (n : ℕ) :
    ‖realSpectralState t n‖ ≤ 1 := by
  rw [norm_realSpectralState]
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  · norm_num

/-- Infinite native real-spectral state dressed by the vertical carry amplitude
ratio `q^n`. -/
def nativeCarryWeightedRealSpectralState
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (t : ℝ) : CarryVerticalL2 :=
  ⟨fun n : ℕ => (q : ℂ) ^ n * realSpectralState t n, by
    refine (lp.memℓp (carryGeometricAmplitudeVector q hq0 hq1)).mono' ?_
    intro n
    rw [carryGeometricAmplitudeVector_apply, norm_mul]
    calc
      ‖(q : ℂ) ^ n‖ * ‖realSpectralState t n‖ ≤
          ‖(q : ℂ) ^ n‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_realSpectralState_le_one t n)
          (norm_nonneg _)
      _ = ‖(q : ℂ) ^ n‖ := by ring⟩

@[simp] theorem nativeCarryWeightedRealSpectralState_apply
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (t : ℝ) (n : ℕ) :
    nativeCarryWeightedRealSpectralState q hq0 hq1 t n =
      (q : ℂ) ^ n * realSpectralState t n := rfl

/-- The initial weighted coordinate is the unit seed. -/
@[simp] theorem nativeCarryWeightedRealSpectralState_zero
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (t : ℝ) :
    nativeCarryWeightedRealSpectralState q hq0 hq1 t 0 = 1 := by
  simp [nativeCarryWeightedRealSpectralState, realSpectralState,
    positiveDirichletValue]

/-- The first positive coordinate is `q` times the first real-spectral vertex. -/
@[simp] theorem nativeCarryWeightedRealSpectralState_one
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (t : ℝ) :
    nativeCarryWeightedRealSpectralState q hq0 hq1 t 1 =
      (q : ℂ) * realSpectralState t 1 := by
  simp [nativeCarryWeightedRealSpectralState]

/-- The vertical value--flux trace of the infinite native state is explicit:
unit value and the first undressed phase increment. -/
theorem carryWeightedVerticalTrace_nativeSpectralState
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) (t : ℝ) :
    carryWeightedVerticalTrace q
        (nativeCarryWeightedRealSpectralState q hqpos.le hq1 t) =
      ((1 : ℂ), realSpectralState t 1 - 1) := by
  rw [carryWeightedVerticalTrace_apply]
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hqpos.ne'
  simp [hqC]

/-- After dressing, the vertical bracket is exactly the ordinary centered second
difference of the undressed native orbit, times the common amplitude factor. -/
theorem carryWeightedVerticalCenteredBracket_nativeSpectralState_succ
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (t : ℝ) (n : ℕ) :
    carryWeightedVerticalCenteredBracket q
        (nativeCarryWeightedRealSpectralState q hqpos.le hq1 t) (n + 1) =
      (q : ℂ) ^ (n + 1) *
        (realSpectralState t (n + 2) -
          2 * realSpectralState t (n + 1) +
            realSpectralState t n) := by
  rw [carryWeightedVerticalCenteredBracket_succ]
  simp only [nativeCarryWeightedRealSpectralState_apply]
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hqpos.ne'
  simp only [pow_succ]
  field_simp [hqC]
  ring

/-- Specialization to the material carry ratio of a base `p`. -/
def primeCarryWeightedRealSpectralState
    (p : ℕ) (hp : 2 ≤ p) (t : ℝ) : CarryVerticalL2 :=
  nativeCarryWeightedRealSpectralState (primeCarryAmplitudeRatio p)
    (primeCarryAmplitudeRatio_nonneg p)
    (primeCarryAmplitudeRatio_lt_one p hp) t

@[simp] theorem primeCarryWeightedRealSpectralState_apply
    (p : ℕ) (hp : 2 ≤ p) (t : ℝ) (n : ℕ) :
    primeCarryWeightedRealSpectralState p hp t n =
      (primeCarryAmplitudeRatio p : ℂ) ^ n * realSpectralState t n := rfl

end

end CPFormal.Analytic.Cp
