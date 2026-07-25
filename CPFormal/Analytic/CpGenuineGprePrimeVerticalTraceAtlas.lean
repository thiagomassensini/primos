import CPFormal.Analytic.CpGenuineGprePrimeVerticalTraceGate

/-!
# Finite-prime atlases for the native vertical trace gate

The preceding modules constructed three descriptions of the same finite Green
bulk coordinate:

* the critical-amplitude prime Green profile;
* the normalized enriched log-jet commutator readout;
* the flux component of the material vertical trace applied to the
  mass-normalized first-level carry fiber.

This module assembles those coordinates over a finite atlas of prime cameras.
It proves exact equality of the resulting Hilbert states and identifies the
uniform-atlas norm bound with the half-abscissa.  Thus the remaining
zero-to-domain problem is stated directly on the provenance-preserving
log-jet data, rather than through an abstract diagonal multiplier.

No uniform bound is inferred from a scalar Genuine zero in this module.
-/

open scoped BigOperators ENNReal

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Finite prime-atlas state formed from the fluxes of the native vertical
traces of the mass-normalized fibers. -/
def primeMassGreenVerticalTraceFiniteState
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) :
    PrimeGreenCameraHilbert :=
  ∑ p ∈ S,
    lp.single 2 p (primeMassGreenVerticalTraceFluxProfile M s p)

/-- The vertical-trace atlas is literally the already constructed critical
Green bulk atlas. -/
theorem primeMassGreenVerticalTraceFiniteState_eq_greenBulkFiniteState
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) :
    primeMassGreenVerticalTraceFiniteState M s S =
      primeGreenBulkFiniteState M s S := by
  unfold primeMassGreenVerticalTraceFiniteState primeGreenBulkFiniteState
  apply Finset.sum_congr rfl
  intro p hp
  rw [primeMassGreenVerticalTraceFluxProfile_eq]

/-- Exact norm ledger for the native vertical trace outputs on a finite prime
atlas. -/
theorem primeMassGreenVerticalTraceFiniteState_norm_sq
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) :
    ‖primeMassGreenVerticalTraceFiniteState M s S‖ ^ 2 =
      ∑ p ∈ S, (primeMassGreenVerticalTraceFluxProfile M s p) ^ 2 := by
  rw [primeMassGreenVerticalTraceFiniteState_eq_greenBulkFiniteState,
    primeGreenBulkFiniteState_norm_sq]
  apply Finset.sum_congr rfl
  intro p hp
  rw [primeMassGreenVerticalTraceFluxProfile_eq]

/-- Uniform graph-output control as the prime atlas grows. -/
def PrimeMassGreenVerticalTraceFiniteStatesBounded
    (M : ℕ) (s : ℂ) : Prop :=
  ∃ C : ℝ, ∀ S : Finset Nat.Primes,
    ‖primeMassGreenVerticalTraceFiniteState M s S‖ ^ 2 ≤ C

/-- Uniform boundedness of the concrete vertical trace atlases is exactly the
critical localization condition. -/
theorem primeMassGreenVerticalTraceFiniteStatesBounded_iff
    (M : ℕ) (hM : 0 < M) {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    PrimeMassGreenVerticalTraceFiniteStatesBounded M s ↔
      criticalDisplacement s.re = 0 := by
  constructor
  · rintro ⟨C, hC⟩
    apply (primeGreenBulkFiniteStatesBounded_iff M hM hs).1
    refine ⟨C, ?_⟩
    intro S
    rw [← primeMassGreenVerticalTraceFiniteState_eq_greenBulkFiniteState]
    exact hC S
  · intro hcritical
    have hgreen :=
      (primeGreenBulkFiniteStatesBounded_iff M hM hs).2 hcritical
    rcases hgreen with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro S
    rw [primeMassGreenVerticalTraceFiniteState_eq_greenBulkFiniteState]
    exact hC S

/-- Canonical enriched log-jet readout state on a finite atlas.  Unit valve
scales are used only to avoid carrying irrelevant nonzero parameters. -/
def canonicalEnrichedGpreLogJetGreenAtlasState
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) :
    PrimeGreenCameraHilbert :=
  ∑ p ∈ S,
    lp.single 2 p
      (finiteEnrichedNativeGpreLogJetGreenBulkReadout
        p M 1 (fun _ => 1) s)

/-- Coordinatewise, the canonical enriched log-jet readout is the flux of the
native vertical trace applied to the mass fiber at the aligned cutoff `3M`. -/
theorem finiteEnrichedNativeGpreLogJetGreenBulkReadout_eq_verticalTraceFlux
    (p : Nat.Primes) (M : ℕ) (s : ℂ) :
    finiteEnrichedNativeGpreLogJetGreenBulkReadout
        p M 1 (fun _ => 1) s =
      primeMassGreenVerticalTraceFluxProfile (3 * M) s p := by
  rw [finiteEnrichedNativeGpreLogJetGreenBulkReadout_eq
      p M (by norm_num) (fun _ => 1) (by intro m; norm_num) s,
    primeMassGreenVerticalTraceFluxProfile_eq]

/-- Equality of complete finite-atlas states: provenance-preserving log-jet
wedges and native vertical trace fluxes are the same vector. -/
theorem canonicalEnrichedGpreLogJetGreenAtlasState_eq_verticalTraceFiniteState
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) :
    canonicalEnrichedGpreLogJetGreenAtlasState M s S =
      primeMassGreenVerticalTraceFiniteState (3 * M) s S := by
  unfold canonicalEnrichedGpreLogJetGreenAtlasState
    primeMassGreenVerticalTraceFiniteState
  apply Finset.sum_congr rfl
  intro p hp
  rw [finiteEnrichedNativeGpreLogJetGreenBulkReadout_eq_verticalTraceFlux]

/-- Exact norm ledger written entirely in the enriched log-jet readout
coordinates. -/
theorem canonicalEnrichedGpreLogJetGreenAtlasState_norm_sq
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) :
    ‖canonicalEnrichedGpreLogJetGreenAtlasState M s S‖ ^ 2 =
      ∑ p ∈ S,
        (finiteEnrichedNativeGpreLogJetGreenBulkReadout
          p M 1 (fun _ => 1) s) ^ 2 := by
  simpa [canonicalEnrichedGpreLogJetGreenAtlasState, Real.norm_eq_abs,
    sq_abs] using
    (lp.norm_sum_single
      (E := fun _ : Nat.Primes => ℝ)
      (p := (2 : ℝ≥0∞)) (by norm_num)
      (fun p : Nat.Primes =>
        finiteEnrichedNativeGpreLogJetGreenBulkReadout
          p M 1 (fun _ => 1) s) S)

/-- Uniform boundedness stated directly on the enriched `G_pre` log-jet
readout atlases. -/
def CanonicalEnrichedGpreLogJetGreenAtlasesBounded
    (M : ℕ) (s : ℂ) : Prop :=
  ∃ C : ℝ, ∀ S : Finset Nat.Primes,
    ‖canonicalEnrichedGpreLogJetGreenAtlasState M s S‖ ^ 2 ≤ C

/-- At any nonempty angular cutoff, uniform boundedness of the enriched
log-jet atlases is exactly the half-abscissa. -/
theorem canonicalEnrichedGpreLogJetGreenAtlasesBounded_iff
    (M : ℕ) (hM : 0 < M) {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    CanonicalEnrichedGpreLogJetGreenAtlasesBounded M s ↔
      criticalDisplacement s.re = 0 := by
  constructor
  · rintro ⟨C, hC⟩
    apply
      (primeMassGreenVerticalTraceFiniteStatesBounded_iff
        (3 * M) (by positivity) hs).1
    refine ⟨C, ?_⟩
    intro S
    rw [← canonicalEnrichedGpreLogJetGreenAtlasState_eq_verticalTraceFiniteState]
    exact hC S
  · intro hcritical
    have htrace :=
      (primeMassGreenVerticalTraceFiniteStatesBounded_iff
        (3 * M) (by positivity) hs).2 hcritical
    rcases htrace with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro S
    rw [canonicalEnrichedGpreLogJetGreenAtlasState_eq_verticalTraceFiniteState]
    exact hC S

/-- The remaining global assertion in the concrete enriched-atlas language. -/
def GenuineZerosBoundCanonicalEnrichedGpreLogJetGreenAtlases : Prop :=
  ∀ {s : ℂ}, genuineContinuation s = 0 →
    s ∈ genuineCriticalStrip →
      CanonicalEnrichedGpreLogJetGreenAtlasesBounded 1 s

/-- Scope guard: proving the uniform enriched-atlas estimate at every Genuine
zero has exactly the strength of strong nonvanishing off the half-abscissa. -/
theorem genuineZerosBoundCanonicalEnrichedGpreLogJetGreenAtlases_iff_strongNonvanishing :
    GenuineZerosBoundCanonicalEnrichedGpreLogJetGreenAtlases ↔
      GenuineStrongNonvanishingInStrip := by
  constructor
  · intro hbound s hs hoff hzero
    have hcritical :=
      (canonicalEnrichedGpreLogJetGreenAtlasesBounded_iff
        1 (by norm_num) hs).1 (hbound hzero hs)
    apply hoff
    unfold criticalDisplacement at hcritical
    linarith
  · intro hstrong s hzero hs
    apply
      (canonicalEnrichedGpreLogJetGreenAtlasesBounded_iff
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
