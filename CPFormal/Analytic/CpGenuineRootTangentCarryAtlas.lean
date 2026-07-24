import CPFormal.Analytic.CpGenuineRootTangentCarryCrosswalk

/-!
# Finite prime-atlas states constructed from Genuine root tangents

The root-tangent crosswalk reconstructs each enriched prime Green readout from
the tangent of the corresponding camera product at a simple Genuine zero and
at its reflected zero.  This module assembles those root-derived coefficients
in the centered-carry dual axes.

For every finite prime atlas the resulting state is proved to be exactly the
canonical provenance state already used in the unweighted Bessel ledger.  Thus
finite realization truly comes from the root data, not from a later definition
using the Green target.

The final theorem keeps the logical boundary explicit: uniform boundedness of
these root-derived finite-atlas states is equivalent to the half-abscissa.  A
simple root supplies all finite coordinates, but it does not by itself prove
the uniform Hilbert completion.
-/

open scoped BigOperators ENNReal

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Local centered-carry state whose coefficient is reconstructed from the
Genuine root tangents.  The cutoff `3M` matches the three Green edges returned
by each enriched TFVD block. -/
def genuineRootTangentPrimeCarryDefectState
    (p : Nat.Primes) (M : ℕ) (s : ℂ) : PrimeCarryResidueHilbert p :=
  genuineRootTangentGreenBulk p (3 * M) s •
    primeCriticalCenteredCarryDualAxis p

/-- At a reflected simple-root pair, the root-derived local state is exactly
the independently defined enriched provenance state. -/
theorem genuineRootTangentPrimeCarryDefectState_eq_provenanceState
    (p : Nat.Primes) (M : ℕ) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hsimple : deriv genuineContinuation s ≠ 0)
    (hsimpleSharp :
      deriv genuineContinuation (reflectedParameter s) ≠ 0) :
    genuineRootTangentPrimeCarryDefectState p M s =
      finiteEnrichedPrimeCarryDefectProvenanceState
        p M 1 (fun _ => 1) s := by
  unfold genuineRootTangentPrimeCarryDefectState
    finiteEnrichedPrimeCarryDefectProvenanceState
  rw [genuineRootTangentGreenBulk_eq
      p (3 * M) hs hzero hsimple hsimpleSharp,
    finiteEnrichedNativeGpreLogJetGreenBulkReadout_eq
      p M (by norm_num) (fun _ => 1) (by intro m; norm_num) s]

/-- One common finite-atlas state assembled entirely from root-tangent
coefficients before any global completion is requested. -/
def genuineRootTangentPrimeCarryDefectAtlasState
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) :
    PrimeCarryDefectGlobalHilbert :=
  ∑ p ∈ S,
    lp.single 2 p (genuineRootTangentPrimeCarryDefectState p M s)

/-- Every finite root-tangent atlas is exactly the canonical centered-carry
provenance atlas. -/
theorem genuineRootTangentPrimeCarryDefectAtlasState_eq_canonical
    (M : ℕ) (S : Finset Nat.Primes) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hsimple : deriv genuineContinuation s ≠ 0)
    (hsimpleSharp :
      deriv genuineContinuation (reflectedParameter s) ≠ 0) :
    genuineRootTangentPrimeCarryDefectAtlasState M s S =
      canonicalEnrichedPrimeCarryDefectProvenanceState M s S := by
  unfold genuineRootTangentPrimeCarryDefectAtlasState
    canonicalEnrichedPrimeCarryDefectProvenanceState
  apply Finset.sum_congr rfl
  intro p hp
  rw [genuineRootTangentPrimeCarryDefectState_eq_provenanceState
    p M hs hzero hsimple hsimpleSharp]

/-- Uniform Hilbert control of all finite states assembled from the root
tangents. -/
def GenuineRootTangentPrimeCarryDefectAtlasStatesBounded
    (M : ℕ) (s : ℂ) : Prop :=
  ∃ C : ℝ, ∀ S : Finset Nat.Primes,
    ‖genuineRootTangentPrimeCarryDefectAtlasState M s S‖ ^ 2 ≤ C

/-- Root-tangent atlas boundedness is the same quantitative condition as
boundedness of the canonical provenance atlases. -/
theorem genuineRootTangentPrimeCarryDefectAtlasStatesBounded_iff_canonical
    (M : ℕ) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hsimple : deriv genuineContinuation s ≠ 0)
    (hsimpleSharp :
      deriv genuineContinuation (reflectedParameter s) ≠ 0) :
    GenuineRootTangentPrimeCarryDefectAtlasStatesBounded M s ↔
      CanonicalEnrichedPrimeCarryDefectProvenanceStatesBounded M s := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro S
    rw [← genuineRootTangentPrimeCarryDefectAtlasState_eq_canonical
      M S hs hzero hsimple hsimpleSharp]
    exact hC S
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro S
    rw [genuineRootTangentPrimeCarryDefectAtlasState_eq_canonical
      M S hs hzero hsimple hsimpleSharp]
    exact hC S

/-- Even when every finite state has been reconstructed from a reflected pair
of simple root tangents, uniform completion occurs exactly at the
half-abscissa. -/
theorem genuineRootTangentPrimeCarryDefectAtlasStatesBounded_iff
    (M : ℕ) (hM : 0 < M) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hsimple : deriv genuineContinuation s ≠ 0)
    (hsimpleSharp :
      deriv genuineContinuation (reflectedParameter s) ≠ 0) :
    GenuineRootTangentPrimeCarryDefectAtlasStatesBounded M s ↔
      criticalDisplacement s.re = 0 := by
  rw [genuineRootTangentPrimeCarryDefectAtlasStatesBounded_iff_canonical
      M hs hzero hsimple hsimpleSharp,
    canonicalEnrichedPrimeCarryDefectProvenanceStatesBounded_iff
      M hM hs]

end

end CPFormal.Analytic.Cp
