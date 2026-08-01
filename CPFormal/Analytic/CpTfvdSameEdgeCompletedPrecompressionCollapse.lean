import CPFormal.Analytic.CpTfvdSameEdgeReflectedEnergyFixedTimeNoGo

/-!
# Completed same-edge precompression collapse

The raw same-edge reflected-energy state cannot be identified with the fixed
native-time moment state: on the critical locus the reflected radial readout is
zero while the common energy itself is strictly positive.

The correct lossless object therefore keeps two channels separate:

* an untransported fixed-time visible channel;
* the reflected precompression energy channel.

This module packages that separation before any claim that the residual energy
has been transported to native time.  For canonical ordinary/log-jet inputs,
the residual channel is exactly the prime-independent first-level Green energy
state.  Its reflected readout is the prime Green bulk, whereas the visible
fixed-time channel remains zero.

At critical displacement every prime readout of the completed pair is zero, but
the completed precompression state is nonzero at every nonempty cutoff in the
Genuine strip.  This is an exact finite point-blind identity: vanishing of the
radial observable does not erase the positive state from which it was formed.

No Genuine zero, Zeta, RH, equation functional, `axiom`, `sorry`, `admit` or
`unsafe` is used.  The construction is an extension of the TFVD--G_pre energy
architecture and does not reopen the already-proved native-operator
confinement.
-/

open scoped ENNReal InnerProduct lp

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Two-channel target: an untransported native-time slot and the residual
precompression energy slot. -/
abbrev NativeGpreTfvdCompletedPrecompressionSource :=
  NativeGpreTowerHilbert × NativeGpreTowerHilbert

/-- A completed collapse keeps the two same-edge inputs but returns both the
visible native-time slot and the residual energy slot. -/
abbrev NativeGpreTfvdCompletedPrecompressionCollapse :=
  NativeGpreTfvdProductState →
    NativeGpreTfvdProductState →
      NativeGpreTfvdCompletedPrecompressionSource

/-- The canonical completed collapse before fixed-time transport.  No visible
native-time source is manufactured; the exactly recovered reflected energy is
retained in the second channel. -/
noncomputable def nativeGpreTfvdSameEdgeCompletedPrecompressionCollapseAt
    (N : ℕ) : NativeGpreTfvdCompletedPrecompressionCollapse :=
  fun ordinary logJet =>
    (0, nativeGpreTfvdSameEdgeReflectedEnergyCollapseAt N ordinary logJet)

/-- Apply a completed collapse to the two canonical same-edge TFVD prefixes. -/
def seededTfvdGpreCompletedPrecompressionSource
    (collapse : NativeGpreTfvdCompletedPrecompressionCollapse)
    (M : ℕ) (s : ℂ) : NativeGpreTfvdCompletedPrecompressionSource :=
  collapse
    (nativeGpreTfvdSameEdgeGlue nativeGpreCanonicalVerticalRealization
      (c2DirichletGradientPrefixCore s (3 * M)))
    (nativeGpreTfvdSameEdgeGlue nativeGpreCanonicalVerticalRealization
      (c2LogJetPrefixCore s (3 * M)))

/-- On canonical data, the completed source is exactly zero in the
untransported visible slot and the common Green energy state in the residual
slot. -/
theorem seededTfvdGpreCompletedPrecompressionSource_sameEdge
    (M : ℕ) (s : ℂ) :
    seededTfvdGpreCompletedPrecompressionSource
        (nativeGpreTfvdSameEdgeCompletedPrecompressionCollapseAt (3 * M))
        M s =
      (0, nativeGpreGreenEnergyFirstLevelState (3 * M) s) := by
  change
    (0,
      seededTfvdGpreCollapsedSource
        (nativeGpreTfvdSameEdgeReflectedEnergyCollapseAt (3 * M)) M s) =
      (0, nativeGpreGreenEnergyFirstLevelState (3 * M) s)
  rw [seededTfvdGpreCollapsedSource_sameEdgeReflectedEnergy]

/-- Two-channel readout of one prime camera.  The first coordinate uses the
fixed native profile; the second uses the reflected radial profile. -/
def nativeGpreTfvdCompletedPrecompressionPrimeReadout
    (p : Nat.Primes) (s : ℂ)
    (state : NativeGpreTfvdCompletedPrecompressionSource) : ℝ × ℝ :=
  (inner ℝ (nativeGpreTowerProfileVector (p : ℕ) 1) state.1,
    inner ℝ (nativeGpreReflectedFirstLevelGapProfile p s) state.2)

/-- Exact readout of the canonical completed source: no fixed-time value is
inserted, while the residual channel reproduces the existing prime Green bulk. -/
theorem nativeGpreTfvdCompletedPrecompressionPrimeReadout_sameEdge
    (M : ℕ) (s : ℂ) (p : Nat.Primes) :
    nativeGpreTfvdCompletedPrecompressionPrimeReadout p s
        (seededTfvdGpreCompletedPrecompressionSource
          (nativeGpreTfvdSameEdgeCompletedPrecompressionCollapseAt (3 * M))
          M s) =
      (0, primeCarryGreenBulkCutoffProfile (3 * M) s p) := by
  rw [seededTfvdGpreCompletedPrecompressionSource_sameEdge]
  unfold nativeGpreTfvdCompletedPrecompressionPrimeReadout
  simp only [Prod.fst, Prod.snd, inner_zero_right]
  rw [inner_nativeGpreReflectedFirstLevelGapProfile_eq_greenBulk]

/-- At critical displacement both observable coordinates vanish. -/
theorem nativeGpreTfvdCompletedPrecompressionPrimeReadout_eq_zero_of_critical
    (M : ℕ) (s : ℂ) (p : Nat.Primes)
    (hcritical : criticalDisplacement s.re = 0) :
    nativeGpreTfvdCompletedPrecompressionPrimeReadout p s
        (seededTfvdGpreCompletedPrecompressionSource
          (nativeGpreTfvdSameEdgeCompletedPrecompressionCollapseAt (3 * M))
          M s) =
      0 := by
  rw [nativeGpreTfvdCompletedPrecompressionPrimeReadout_sameEdge,
    primeCarryGreenBulkCutoffProfile_eq]
  simp [hcritical, primeCarryGreenRadialProfile, cpRadialDifference]

/-- The common first-level Green energy state is nonzero at every nonempty
cutoff in the Genuine strip. -/
theorem nativeGpreGreenEnergyFirstLevelState_ne_zero
    {M : ℕ} (hM : 0 < M) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip) :
    nativeGpreGreenEnergyFirstLevelState M s ≠ 0 := by
  intro hzero
  have hcoord := congrArg
    (fun x : NativeGpreTowerHilbert => x 1) hzero
  have hpos := finiteReflectedGradientPairing_re_pos hM hs
  simp [nativeGpreGreenEnergyFirstLevelState, lp.single_apply] at hcoord
  rw [hcoord] at hpos
  exact (lt_irrefl 0) hpos

/-- Consequently the completed precompression source is nonzero, even though
its visible slot is zero. -/
theorem seededTfvdGpreCompletedPrecompressionSource_ne_zero
    {M : ℕ} (hM : 0 < M) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip) :
    seededTfvdGpreCompletedPrecompressionSource
        (nativeGpreTfvdSameEdgeCompletedPrecompressionCollapseAt (3 * M))
        M s ≠ 0 := by
  rw [seededTfvdGpreCompletedPrecompressionSource_sameEdge]
  intro hzero
  have hsnd := congrArg Prod.snd hzero
  apply nativeGpreGreenEnergyFirstLevelState_ne_zero (by omega) hs
  simpa using hsnd

/-- Exact point-blind checkpoint: at critical displacement all prime readouts
of the completed pair vanish, while the underlying completed precompression
state remains nonzero. -/
theorem completedSameEdgePrecompression_pointBlindAtCritical
    {M : ℕ} (hM : 0 < M) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (hcritical : criticalDisplacement s.re = 0) :
    (∀ p : Nat.Primes,
      nativeGpreTfvdCompletedPrecompressionPrimeReadout p s
          (seededTfvdGpreCompletedPrecompressionSource
            (nativeGpreTfvdSameEdgeCompletedPrecompressionCollapseAt (3 * M))
            M s) = 0) ∧
      seededTfvdGpreCompletedPrecompressionSource
          (nativeGpreTfvdSameEdgeCompletedPrecompressionCollapseAt (3 * M))
          M s ≠ 0 := by
  constructor
  · intro p
    exact
      nativeGpreTfvdCompletedPrecompressionPrimeReadout_eq_zero_of_critical
        M s p hcritical
  · exact seededTfvdGpreCompletedPrecompressionSource_ne_zero hM hs

end

end CPFormal.Analytic.Cp
