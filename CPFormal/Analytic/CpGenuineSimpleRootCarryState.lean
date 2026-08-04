import CPFormal.Analytic.CpGenuineRootTangentCarryAtlas
import CPFormal.Analytic.CpGenuinePrimeCarryDefectUniformBound

/-!
# Multiplicity-one Genuine roots and the global mass state

This module closes the parts of the root-tangent route which use only a
multiplicity-one Genuine zero.

* simplicity is transported automatically to the reflected zero;
* the reflected tangent hypothesis is removed from all finite-atlas
  crosswalks;
* one global square-summable **mass** state is constructed directly from the
  root tangents;
* its native primewise vertical trace is exactly the critical-amplitude Green
  readout.

The last distinction remains explicit.  The mass state belongs to the global
Hilbert space throughout the open strip, while simultaneous square summability
of its trace outputs is equivalent to critical localization.  Thus no
zero-to-trace-domain or zero-to-centered-carry-state instance is declared.
Zeros of higher multiplicity are not treated in this module.
-/

open scoped BigOperators ENNReal Topology ComplexConjugate

namespace CPFormal.Analytic.Cp

open Filter Set Complex

noncomputable section

/-- A Genuine zero of multiplicity one in the open strip whose reflected
parameter is also a simple point.  Both simplicities are **explicit**
hypotheses: no functional equation / zeta reflection is used to derive the
second.  Natively there is no `σ ↦ 1-σ` symmetry, so the reflected simplicity
is assumed here, not borrowed from zeta. -/
def IsSimpleGenuineZeroInStrip (s : ℂ) : Prop :=
  s ∈ genuineCriticalStrip ∧
    genuineContinuation s = 0 ∧
      deriv genuineContinuation s ≠ 0 ∧
        deriv genuineContinuation (reflectedParameter s) ≠ 0

/-- The open critical strip is an open subset of the complex plane. -/
theorem isOpen_genuineCriticalStrip : IsOpen genuineCriticalStrip := by
  change IsOpen ({s : ℂ | 0 < s.re} ∩ {s : ℂ | s.re < 1})
  exact
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)

/-- Conjugation preserves the open critical strip. -/
theorem conj_mem_genuineCriticalStrip
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    (starRingEnd ℂ) s ∈ genuineCriticalStrip := by
  simpa [genuineCriticalStrip] using hs

/-- For a multiplicity-one zero, one root tangent recovers the prime Green
bulk.  The reflected simplicity is the explicit fourth field of
`IsSimpleGenuineZeroInStrip` (assumed, not zeta-derived). -/
theorem genuineRootTangentGreenBulk_eq_of_simple_zero
    (p : Nat.Primes) (M : ℕ) {s : ℂ}
    (hroot : IsSimpleGenuineZeroInStrip s) :
    genuineRootTangentGreenBulk p M s =
      primeCarryGreenBulkCutoffProfile M s p := by
  rcases hroot with ⟨hs, hzero, hsimple, hsharp⟩
  exact genuineRootTangentGreenBulk_eq p M hs hzero hsimple hsharp

/-- Every finite multiplicity-one root-tangent atlas is the canonical
centered-carry provenance atlas.  The reflected simplicity is the explicit
fourth field of `IsSimpleGenuineZeroInStrip`. -/
theorem genuineRootTangentPrimeCarryDefectAtlasState_eq_canonical_of_simple_zero
    (M : ℕ) (S : Finset Nat.Primes) {s : ℂ}
    (hroot : IsSimpleGenuineZeroInStrip s) :
    genuineRootTangentPrimeCarryDefectAtlasState M s S =
      canonicalEnrichedPrimeCarryDefectProvenanceState M s S := by
  rcases hroot with ⟨hs, hzero, hsimple, hsharp⟩
  exact genuineRootTangentPrimeCarryDefectAtlasState_eq_canonical
    M S hs hzero hsimple hsharp

/-- Local mass fiber reconstructed from the multiplicity-one root tangent. -/
def genuineRootTangentMassVerticalFiberState
    (p : Nat.Primes) (M : ℕ) (s : ℂ) : CarryVerticalL2 :=
  lp.single 2 1
    ((primeCarryAmplitudeRatio p * genuineRootTangentGreenBulk p M s : ℝ) : ℂ)

/-- At a simple root the root-tangent mass fiber is the previously certified
mass Green fiber. -/
theorem genuineRootTangentMassVerticalFiberState_eq_massFiber
    (p : Nat.Primes) (M : ℕ) {s : ℂ}
    (hroot : IsSimpleGenuineZeroInStrip s) :
    genuineRootTangentMassVerticalFiberState p M s =
      primeMassGreenVerticalFiberState M s p := by
  unfold genuineRootTangentMassVerticalFiberState
    primeMassGreenVerticalFiberState
  congr 2
  rw [genuineRootTangentGreenBulk_eq_of_simple_zero p M hroot]
  exact (primeMassGreenBulkCutoffProfile_eq_amplitude_mul M s p).symm

/-- The globally square-summable mass state associated with a simple Genuine
root.  Its coordinate formula below shows that it is reconstructed by the root
tangents, although the existing mass-state constructor supplies the Hilbert
membership proof. -/
def genuineSimpleRootMassVerticalGlobalState
    (M : ℕ) (s : ℂ) (hroot : IsSimpleGenuineZeroInStrip s) :
    PrimeCarryVerticalHilbert :=
  primeMassGreenVerticalGlobalState M s hroot.1

/-- Prime coordinates of the global mass state are the root-tangent mass
fibers. -/
theorem genuineSimpleRootMassVerticalGlobalState_apply
    (M : ℕ) (s : ℂ) (hroot : IsSimpleGenuineZeroInStrip s)
    (p : Nat.Primes) :
    genuineSimpleRootMassVerticalGlobalState M s hroot p =
      genuineRootTangentMassVerticalFiberState p M s := by
  rw [genuineSimpleRootMassVerticalGlobalState,
    primeMassGreenVerticalGlobalState_apply,
    genuineRootTangentMassVerticalFiberState_eq_massFiber p M hroot]

/-- The native vertical trace of the global root-derived mass state recovers
exactly the root-tangent Green bulk in every prime camera. -/
theorem primeCarryWeightedVerticalTrace_simpleRootMassState
    (M : ℕ) (s : ℂ) (hroot : IsSimpleGenuineZeroInStrip s)
    (p : Nat.Primes) :
    primeCarryWeightedVerticalTrace (p : ℕ)
        (genuineSimpleRootMassVerticalGlobalState M s hroot p) =
      (0, (genuineRootTangentGreenBulk p M s : ℂ)) := by
  rw [genuineSimpleRootMassVerticalGlobalState_apply,
    genuineRootTangentMassVerticalFiberState_eq_massFiber p M hroot,
    primeCarryWeightedVerticalTrace_massFiber,
    genuineRootTangentGreenBulk_eq_of_simple_zero p M hroot]

/-- Global trace-domain condition for the root-derived multiplicity-one mass
state. -/
def SimpleRootMassVerticalGlobalTraceDomainAt
    (M : ℕ) (s : ℂ) (hroot : IsSimpleGenuineZeroInStrip s) : Prop :=
  Summable (fun p : Nat.Primes =>
    ((primeCarryWeightedVerticalTrace (p : ℕ)
      (genuineSimpleRootMassVerticalGlobalState M s hroot p)).2.re) ^ 2)

/-- Exact endpoint of the multiplicity-one construction: the root-derived mass
state always exists globally, but its simultaneous trace belongs to `ell^2`
exactly on the half-abscissa. -/
theorem simpleRootMassVerticalGlobalTraceDomainAt_iff
    (M : ℕ) (hM : 0 < M) {s : ℂ}
    (hroot : IsSimpleGenuineZeroInStrip s) :
    SimpleRootMassVerticalGlobalTraceDomainAt M s hroot ↔
      criticalDisplacement s.re = 0 := by
  unfold SimpleRootMassVerticalGlobalTraceDomainAt
  have hfun :
      (fun p : Nat.Primes =>
        ((primeCarryWeightedVerticalTrace (p : ℕ)
          (genuineSimpleRootMassVerticalGlobalState M s hroot p)).2.re) ^ 2) =
      (fun p : Nat.Primes =>
        (primeCarryGreenBulkCutoffProfile M s p) ^ 2) := by
    funext p
    rw [primeCarryWeightedVerticalTrace_simpleRootMassState,
      genuineRootTangentGreenBulk_eq_of_simple_zero p M hroot]
    simp
  rw [hfun]
  exact summable_primeCarryGreenBulkCutoffProfile_sq_iff
    M hM hroot.1

/-- The multiplicity-one strong statement, separated from possible higher
multiplicity zeros. -/
def GenuineSimpleZerosAreCritical : Prop :=
  ∀ {s : ℂ}, IsSimpleGenuineZeroInStrip s →
    criticalDisplacement s.re = 0

/-- Global centered-carry-state formulation restricted to multiplicity-one
zeros. -/
def GenuineSimpleZerosAdmitGlobalCenteredCarryReadoutState : Prop :=
  ∀ {s : ℂ}, IsSimpleGenuineZeroInStrip s →
    ∃ x : PrimeCarryDefectGlobalHilbert,
      IsCanonicalEnrichedPrimeCarryDefectReadoutRealization 1 s x

/-- For multiplicity-one zeros, the global state construction and critical
localization are exactly equivalent.  This scope guard leaves the final
uniform completion premise visible rather than declaring it from simplicity. -/
theorem genuineSimpleZerosAdmitGlobalCenteredCarryReadoutState_iff_critical :
    GenuineSimpleZerosAdmitGlobalCenteredCarryReadoutState ↔
      GenuineSimpleZerosAreCritical := by
  constructor
  · intro hstate s hroot
    exact
      (exists_globalCarryDefectReadoutRealization_iff
        1 (by norm_num) hroot.1).1 (hstate hroot)
  · intro hcritical s hroot
    exact
      (exists_globalCarryDefectReadoutRealization_iff
        1 (by norm_num) hroot.1).2 (hcritical hroot)

end

end CPFormal.Analytic.Cp
