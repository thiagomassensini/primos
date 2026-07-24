import CPFormal.Analytic.CpGenuineGreenKernelInclusion

/-!
# Genuine--G_pre prime-moment crosswalk at the first tower level

The centered Green bulk of a prime camera has the exact coefficient

`p^(re(s)-1) - p^(-re(s))`.

This module realizes that coefficient without defining a state from the target
coordinates.  A single first-level energy state, independent of the prime, is
paired against the difference of two first-level `G_pre` profiles at the
reflected real times `1-re(s)` and `re(s)`.

Thus the Green bulk is already a universal Hilbert moment.  The remaining gate
is sharper: move the spectral dependence from this reflected profile family to
the fixed native family at arithmetic time `tau = 1`, while retaining one
state for all prime cameras.  The kernel proves that existence of precisely
that fixed-time realization is equivalent to the half-abscissa; no instance is
declared from a Genuine zero.
-/

open scoped ENNReal

namespace CPFormal.Analytic.Cp

noncomputable section

/-- First-level extension of the native tower profile to a real time `tau`.
Only level `1` is populated, so no summability theorem for the full real-time
tower is hidden in this definition. -/
def nativeGpreRealTimeFirstLevelProfile
    (p : Nat.Primes) (tau : ℝ) : NativeGpreTowerHilbert :=
  lp.single 2 1 ((p : ℝ) ^ (-tau))

/-- Difference of the two reflected real-time first-level profiles. -/
def nativeGpreReflectedFirstLevelGapProfile
    (p : Nat.Primes) (s : ℂ) : NativeGpreTowerHilbert :=
  nativeGpreRealTimeFirstLevelProfile p (1 - s.re) -
    nativeGpreRealTimeFirstLevelProfile p s.re

/-- The common reflected Green energy stored at the first tower level.  This
state depends on `M,s` but not on the prime camera. -/
def nativeGpreGreenEnergyFirstLevelState
    (M : ℕ) (s : ℂ) : NativeGpreTowerHilbert :=
  lp.single 2 1 (finiteReflectedGradientPairing M s).re

/-- A first-level real-time profile reads the common energy with coefficient
`p^(-tau)`. -/
theorem inner_nativeGpreRealTimeFirstLevelProfile_greenEnergyState
    (p : Nat.Primes) (tau : ℝ) (M : ℕ) (s : ℂ) :
    inner ℝ (nativeGpreRealTimeFirstLevelProfile p tau)
        (nativeGpreGreenEnergyFirstLevelState M s) =
      (p : ℝ) ^ (-tau) * (finiteReflectedGradientPairing M s).re := by
  classical
  unfold nativeGpreRealTimeFirstLevelProfile
    nativeGpreGreenEnergyFirstLevelState
  rw [lp.inner_single_left]
  simp [lp.single_apply]
  ring

/-- The reflected first-level gap is exactly the two-exponent Dirichlet gap
appearing in the carry-dressed Green camera. -/
theorem inner_nativeGpreReflectedFirstLevelGapProfile_greenEnergyState
    (p : Nat.Primes) (M : ℕ) (s : ℂ) :
    inner ℝ (nativeGpreReflectedFirstLevelGapProfile p s)
        (nativeGpreGreenEnergyFirstLevelState M s) =
      ((p : ℝ) ^ (s.re - 1) - (p : ℝ) ^ (-s.re)) *
        (finiteReflectedGradientPairing M s).re := by
  rw [nativeGpreReflectedFirstLevelGapProfile, inner_sub_left,
    inner_nativeGpreRealTimeFirstLevelProfile_greenEnergyState,
    inner_nativeGpreRealTimeFirstLevelProfile_greenEnergyState]
  have hexponent : -(1 - s.re) = s.re - 1 := by ring
  rw [hexponent]
  ring

/-- Exact universal-state crosswalk: every centered prime Green bulk is the
moment of the same energy state against its reflected first-level `G_pre`
profile gap. -/
theorem inner_nativeGpreReflectedFirstLevelGapProfile_eq_greenBulk
    (M : ℕ) (s : ℂ) (p : Nat.Primes) :
    inner ℝ (nativeGpreReflectedFirstLevelGapProfile p s)
        (nativeGpreGreenEnergyFirstLevelState M s) =
      primeCarryGreenBulkCutoffProfile M s p := by
  rw [inner_nativeGpreReflectedFirstLevelGapProfile_greenEnergyState,
    primeCarryGreenBulkCutoffProfile_eq_reflectedDirichletGap_mul]

/-- The precise fixed-time transport target.  The right-hand moments are
already produced by one universal state, but against a spectral profile family.
The proposition asks for one state whose moments against the native fixed-time
profiles `rho_(p,1)` reproduce the same values for all prime cameras. -/
def NativeGpreReflectedGapHasFixedTimeMomentStateAt
    (M : ℕ) (s : ℂ) : Prop :=
  ∃ x : NativeGpreTowerHilbert,
    ∀ p : Nat.Primes,
      inner ℝ (nativeGpreTowerProfileVector (p : ℕ) 1) x =
        inner ℝ (nativeGpreReflectedFirstLevelGapProfile p s)
          (nativeGpreGreenEnergyFirstLevelState M s)

/-- The new fixed-time target is literally the existing native prime-moment
realization predicate after applying the exact universal-state crosswalk. -/
theorem nativeGpreReflectedGapHasFixedTimeMomentStateAt_iff_nativeRealization
    (M : ℕ) (s : ℂ) :
    NativeGpreReflectedGapHasFixedTimeMomentStateAt M s ↔
      ∃ x : NativeGpreTowerHilbert,
        IsNativeGprePrimeMomentRealizationAt 1 M s x := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    intro p
    exact (hx p).trans
      (inner_nativeGpreReflectedFirstLevelGapProfile_eq_greenBulk M s p)
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    intro p
    exact (hx p).trans
      (inner_nativeGpreReflectedFirstLevelGapProfile_eq_greenBulk M s p).symm

/-- At every nonempty Green cutoff, transporting the reflected real-time
profiles to one fixed native-time state is possible exactly on the
half-abscissa. -/
theorem nativeGpreReflectedGapHasFixedTimeMomentStateAt_iff_critical
    (M : ℕ) (hM : 0 < M) {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    NativeGpreReflectedGapHasFixedTimeMomentStateAt M s ↔
      criticalDisplacement s.re = 0 := by
  rw [nativeGpreReflectedGapHasFixedTimeMomentStateAt_iff_nativeRealization]
  exact exists_isNativeGprePrimeMomentRealizationAt_iff
    1 (by norm_num) M hM hs

/-- Global formulation of the remaining bridge in the new crosswalk language. -/
def GenuineZerosProduceNativeGpreFixedTimeMomentCrosswalk : Prop :=
  ∀ {s : ℂ}, genuineContinuation s = 0 →
    s ∈ genuineCriticalStrip →
      NativeGpreReflectedGapHasFixedTimeMomentStateAt 1 s

/-- Scope guard: promoting the exact reflected-profile crosswalk to a fixed
native-time moment state at every Genuine zero has exactly the strength of
strong Genuine nonvanishing off the half-abscissa. -/
theorem genuineZerosProduceNativeGpreFixedTimeMomentCrosswalk_iff_strongNonvanishing :
    GenuineZerosProduceNativeGpreFixedTimeMomentCrosswalk ↔
      GenuineStrongNonvanishingInStrip := by
  constructor
  · intro hcrosswalk s hs hoff hzero
    have hmoment := hcrosswalk hzero hs
    have hdelta :=
      (nativeGpreReflectedGapHasFixedTimeMomentStateAt_iff_critical
        1 (by norm_num) hs).1 hmoment
    apply hoff
    unfold criticalDisplacement at hdelta
    linarith
  · intro hstrong s hzero hs
    apply
      (nativeGpreReflectedGapHasFixedTimeMomentStateAt_iff_critical
        1 (by norm_num) hs).2
    by_contra hdelta
    have hoff : s.re ≠ (1 : ℝ) / 2 := by
      intro hhalf
      apply hdelta
      unfold criticalDisplacement
      rw [hhalf]
      ring
    exact (hstrong hs hoff) hzero

end

end CPFormal.Analytic.Cp
