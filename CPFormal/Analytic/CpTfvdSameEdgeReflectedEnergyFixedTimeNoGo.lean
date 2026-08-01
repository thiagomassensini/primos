import CPFormal.Analytic.CpTfvdSameEdgeReflectedEnergyCollapse

/-!
# Fixed-time no-go for the raw same-edge reflected-energy state

The preceding module extracts one genuine, prime-independent material state
from the ordinary/log-jet same-edge pair.  That state stores the positive
reflected Green energy at material level one.

This file tests whether the raw energy state itself can be the fixed-time source
required by `IsSeededTfvdGpreMomentCollapseAt`.  The answer is no, already on
the critical locus:

* the reflected profile gap vanishes when `criticalDisplacement = 0`;
* the fixed native profile at `tau = 1` reads the positive level-one energy as
  `p^(-1) * E`.

Therefore the final collapse cannot merely extract the common energy.  It must
also contain a radial annihilation/transport operation that sends the critical
energy state to the zero fixed-time moment source.  This is a structural
no-go for one candidate map, not a contradiction with existence of the zero
source on the critical locus.

No Genuine zero, Zeta, RH, `axiom`, `sorry` or `admit` is used.
-/

open scoped ENNReal InnerProduct lp

namespace CPFormal.Analytic.Cp

noncomputable section

/-- A fixed native profile reads the level-one common energy with coefficient
`p^(-1)`. -/
theorem inner_nativeGpreTowerProfileVector_greenEnergyFirstLevelState
    (p M : ℕ) (s : ℂ) :
    inner ℝ (nativeGpreTowerProfileVector p 1)
        (nativeGpreGreenEnergyFirstLevelState M s) =
      (p : ℝ)⁻¹ * (finiteReflectedGradientPairing M s).re := by
  unfold nativeGpreGreenEnergyFirstLevelState
  rw [lp.inner_single_right]
  simp [nativeGpreTowerProfileVector_apply,
    nativeUnitMassTowerProfile, RCLike.inner_apply]
  ring

/-- At every nonempty cutoff in the Genuine strip, that fixed-time readout is
strictly positive for every prime camera. -/
theorem inner_nativeGpreTowerProfileVector_greenEnergyFirstLevelState_pos
    (p : Nat.Primes) {M : ℕ} (hM : 0 < M)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    0 < inner ℝ (nativeGpreTowerProfileVector (p : ℕ) 1)
        (nativeGpreGreenEnergyFirstLevelState M s) := by
  rw [inner_nativeGpreTowerProfileVector_greenEnergyFirstLevelState]
  exact mul_pos
    (inv_pos.mpr (by exact_mod_cast p.property.pos))
    (finiteReflectedGradientPairing_re_pos hM hs)

/-- On the critical locus, the reflected profile gap reads zero from the same
explicit source. -/
theorem
    inner_nativeGpreReflectedFirstLevelGapProfile_seededSameEdgeCollapsedSource_eq_zero_of_critical
    (M : ℕ) (p : Nat.Primes) (s : ℂ)
    (hcritical : criticalDisplacement s.re = 0) :
    inner ℝ (nativeGpreReflectedFirstLevelGapProfile p s)
        (seededTfvdGpreCollapsedSource
          (nativeGpreTfvdSameEdgeReflectedEnergyCollapseAt (3 * M)) M s) =
      0 := by
  rw [
    inner_nativeGpreReflectedFirstLevelGapProfile_seededSameEdgeCollapsedSource,
    primeCarryGreenBulkCutoffProfile_eq]
  simp [hcritical, primeCarryGreenRadialProfile, cpRadialDifference]

/-- The raw reflected-energy collapse cannot transport its positive energy
state directly to fixed native time, even when the radial displacement already
vanishes. -/
theorem sameEdgeReflectedEnergyTransportsToFixedTimeAt_not_of_critical
    (p : Nat.Primes) {M : ℕ} (hM : 0 < M)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hcritical : criticalDisplacement s.re = 0) :
    ¬ SameEdgeReflectedEnergyTransportsToFixedTimeAt M s := by
  intro htransport
  have heq := htransport p
  have hfixed :
      0 < inner ℝ (nativeGpreTowerProfileVector (p : ℕ) 1)
          (seededTfvdGpreCollapsedSource
            (nativeGpreTfvdSameEdgeReflectedEnergyCollapseAt (3 * M)) M s) := by
    rw [seededTfvdGpreCollapsedSource_sameEdgeReflectedEnergy]
    exact
      inner_nativeGpreTowerProfileVector_greenEnergyFirstLevelState_pos
        p (by omega) hs
  have hreflected :
      inner ℝ (nativeGpreReflectedFirstLevelGapProfile p s)
          (seededTfvdGpreCollapsedSource
            (nativeGpreTfvdSameEdgeReflectedEnergyCollapseAt (3 * M)) M s) =
        0 :=
    inner_nativeGpreReflectedFirstLevelGapProfile_seededSameEdgeCollapsedSource_eq_zero_of_critical
      M p s hcritical
  rw [hreflected] at heq
  rw [heq] at hfixed
  exact (lt_irrefl 0) hfixed

/-- Equivalently, the natural raw energy collapse is not an instance of the
fixed-time native moment interface on the critical locus. -/
theorem isSeededTfvdGpreMomentCollapseAt_sameEdgeReflectedEnergy_not_of_critical
    (p : Nat.Primes) {M : ℕ} (hM : 0 < M)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hcritical : criticalDisplacement s.re = 0) :
    ¬ IsSeededTfvdGpreMomentCollapseAt
        (nativeGpreTfvdSameEdgeReflectedEnergyCollapseAt (3 * M)) M s := by
  rw [isSeededTfvdGpreMomentCollapseAt_sameEdgeReflectedEnergy_iff]
  exact sameEdgeReflectedEnergyTransportsToFixedTimeAt_not_of_critical
    p hM hs hcritical

end

end CPFormal.Analytic.Cp
