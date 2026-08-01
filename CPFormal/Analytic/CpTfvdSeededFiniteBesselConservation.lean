import CPFormal.Analytic.CpTfvdSeededReconstructionBridgeProbe
import CPFormal.Analytic.CpGenuinePrimeCarryDefectUniformBound

/-!
# Seeded TFVD radial reconstruction and finite Bessel conservation

The seeded TFVD checkpoint isolates, at every cutoff, the pure radial Green
observable

`radialDifference_p(delta) * Re(pairing_(3M))`.

The centered-carry Bessel construction independently reads the same bulk after
one critical carry-amplitude factor `p^(-1/2)` is inserted.  This module proves
the exact finite crosswalk and rewrites the existing Pythagorean Bessel ledger
entirely in terms of the seeded TFVD radial observables.

No zero hypothesis is used in the finite identities.  At a Genuine zero, the
only remaining issue is uniform boundedness of the conserved finite-atlas
energies; the kernel identifies that condition exactly with the half-abscissa.
-/

open scoped BigOperators Topology ENNReal

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-- The enriched centered-carry readout is exactly one critical carry amplitude
multiplying the seeded TFVD radial observable of the same camera and cutoff. -/
theorem
    finiteEnrichedNativeGpreLogJetGreenBulkReadout_eq_carryAmplitude_mul_seededTfvdRadialObservable
    (p : Nat.Primes) (M : ℕ)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    (s : ℂ) :
    finiteEnrichedNativeGpreLogJetGreenBulkReadout
        p M kappa omega s =
      primeCarryAmplitudeRatio p *
        finiteCanonicalSeededTfvdGreenRadialClosureObservable
          (p : ℕ) M kappa omega s := by
  rw [finiteEnrichedNativeGpreLogJetGreenBulkReadout_eq
      p M hkappa omega homega s,
    primeCarryGreenBulkCutoffProfile_eq,
    finiteCanonicalSeededTfvdGreenRadialClosureObservable_eq_radialDifference_mul_pairing
      (p : ℕ) p.prop M hkappa omega homega s]
  unfold primeCarryGreenRadialProfile
  ring

/-- Exact local energy conversion.  The dual centered-carry state stores the
square of the reconstructed radial observable with the residual-cycle weight
`1 / (p - 1)`. -/
theorem
    finiteEnrichedPrimeCarryDefectProvenanceState_norm_sq_eq_seededTfvdRadialObservable
    (p : Nat.Primes) (M : ℕ)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    (s : ℂ) :
    ‖finiteEnrichedPrimeCarryDefectProvenanceState
        p M kappa omega s‖ ^ 2 =
      (finiteCanonicalSeededTfvdGreenRadialClosureObservable
        (p : ℕ) M kappa omega s) ^ 2 / ((p : ℝ) - 1) := by
  rw [finiteEnrichedPrimeCarryDefectProvenanceState_norm_sq,
    finiteEnrichedNativeGpreLogJetGreenBulkReadout_eq_carryAmplitude_mul_seededTfvdRadialObservable
      p M hkappa omega homega s,
    mul_pow,
    primeCarryAmplitudeRatio_sq_eq_inv (p : ℕ)]
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast p.prop.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have hpgt : (1 : ℝ) < (p : ℝ) := by
      exact_mod_cast p.prop.one_lt
    linarith
  field_simp [hp0, hp1]

/-- Finite Bessel energy written directly from the seeded TFVD radial
observables, with the exact residue-cycle weight dictated by the dual axes. -/
def finiteSeededTfvdBesselEnergy
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) : ℝ :=
  ∑ p ∈ S,
    (finiteCanonicalSeededTfvdGreenRadialClosureObservable
      (p : ℕ) M 1 (fun _ => 1) s) ^ 2 / ((p : ℝ) - 1)

/-- Exact finite conservation identity: the norm of the canonical centered-carry
provenance state is literally the seeded TFVD radial Bessel energy. -/
theorem canonicalEnrichedPrimeCarryDefectProvenanceState_norm_sq_eq_finiteSeededTfvdBesselEnergy
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) :
    ‖canonicalEnrichedPrimeCarryDefectProvenanceState M s S‖ ^ 2 =
      finiteSeededTfvdBesselEnergy M s S := by
  rw [canonicalEnrichedPrimeCarryDefectProvenanceState_norm_sq]
  unfold finiteSeededTfvdBesselEnergy
  apply Finset.sum_congr rfl
  intro p hp
  rw [finiteEnrichedNativeGpreLogJetGreenBulkReadout_eq_carryAmplitude_mul_seededTfvdRadialObservable
      p M (by norm_num) (fun _ => 1) (by intro m; norm_num) s,
    mul_pow,
    primeCarryAmplitudeRatio_sq_eq_inv (p : ℕ)]
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast p.prop.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have hpgt : (1 : ℝ) < (p : ℝ) := by
      exact_mod_cast p.prop.one_lt
    linarith
  field_simp [hp0, hp1]

/-- The existing finite Pythagorean Bessel ledger, now expressed entirely in
seeded TFVD radial coordinates:

`total = reconstructed radial camera energy + unused orthogonal residual`.
-/
theorem canonicalProvenanceState_pythagoras_seededTfvdBesselLedger_of_realizesOn
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes)
    (x : PrimeCarryDefectGlobalHilbert)
    (hrealizes :
      IsCanonicalEnrichedPrimeCarryDefectReadoutRealizationOn M s S x) :
    ‖x‖ ^ 2 =
      finiteSeededTfvdBesselEnergy M s S +
        ‖x - canonicalEnrichedPrimeCarryDefectProvenanceState M s S‖ ^ 2 := by
  rw [canonicalProvenanceState_pythagoras_of_realizesOn
    M s S x hrealizes,
    canonicalEnrichedPrimeCarryDefectProvenanceState_norm_sq_eq_finiteSeededTfvdBesselEnergy]

/-- Uniform conservation of the finite seeded TFVD Bessel energies over all
prime atlases. -/
def SeededTfvdFiniteBesselEnergiesBounded
    (M : ℕ) (s : ℂ) : Prop :=
  ∃ C : ℝ, ∀ S : Finset Nat.Primes,
    finiteSeededTfvdBesselEnergy M s S ≤ C

/-- Uniform boundedness of the radial energy ledger is exactly uniform
boundedness of the canonical centered-carry provenance states. -/
theorem seededTfvdFiniteBesselEnergiesBounded_iff_provenanceStatesBounded
    (M : ℕ) (s : ℂ) :
    SeededTfvdFiniteBesselEnergiesBounded M s ↔
      CanonicalEnrichedPrimeCarryDefectProvenanceStatesBounded M s := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro S
    rw [canonicalEnrichedPrimeCarryDefectProvenanceState_norm_sq_eq_finiteSeededTfvdBesselEnergy]
    exact hC S
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro S
    rw [← canonicalEnrichedPrimeCarryDefectProvenanceState_norm_sq_eq_finiteSeededTfvdBesselEnergy]
    exact hC S

/-- At every nonempty cutoff, finite Bessel energy conservation is uniform over
all prime cameras exactly at zero transverse carry displacement. -/
theorem seededTfvdFiniteBesselEnergiesBounded_iff_criticalDisplacement_eq_zero
    (M : ℕ) (hM : 0 < M) {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    SeededTfvdFiniteBesselEnergiesBounded M s ↔
      criticalDisplacement s.re = 0 := by
  rw [seededTfvdFiniteBesselEnergiesBounded_iff_provenanceStatesBounded,
    canonicalEnrichedPrimeCarryDefectProvenanceStatesBounded_iff M hM hs]

/-- The same finite-conservation threshold in the original radial coordinate. -/
theorem seededTfvdFiniteBesselEnergiesBounded_iff_re_eq_half
    (M : ℕ) (hM : 0 < M) {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    SeededTfvdFiniteBesselEnergiesBounded M s ↔
      s.re = (1 : ℝ) / 2 := by
  rw [seededTfvdFiniteBesselEnergiesBounded_iff_criticalDisplacement_eq_zero
    M hM hs]
  unfold criticalDisplacement
  constructor <;> intro h <;> linarith

/-- One green checkpoint joining the zero-side exact TFVD reconstruction to the
finite Bessel conservation identity.  No uniform-atlas conclusion is inserted:
the second conjunct is a cutoffwise algebraic identity valid independently of
the zero. -/
theorem genuine_zero_tfvd_reconstruction_with_finiteBessel_conservation
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (A : Finset NativeGpreBoundaryContext)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    (Tendsto
        (fun M : ℕ ↦
          finiteSeededEnrichedTfvdGenuineReadout M kappa omega
            (canonicalSeededEnrichedTfvdGenuinePort kappa omega s))
        Filter.atTop (nhds 0) ∧
      nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 A ∘L
          nativeGpreFiniteTfvdAnalysis q A =
        ContinuousLinearMap.id ℂ CarryVerticalL2 ∧
      (∀ M : ℕ,
        nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 A
            (c2DirichletGradientPrefixEnrichedAnalysis q A s (3 * M)) =
          nativeGpreCanonicalVerticalRealization
            (c2DirichletGradientPrefixCore s (3 * M))) ∧
      (∀ M : ℕ,
        nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 A
            (c2LogJetPrefixEnrichedAnalysis q A s (3 * M)) =
          nativeGpreCanonicalVerticalRealization
            (c2LogJetPrefixCore s (3 * M))) ∧
      Tendsto
        (fun M : ℕ ↦ finiteCanonicalSeededTfvdGreenMovingEndpoint M s)
        Filter.atTop (nhds 0)) ∧
    (∀ M : ℕ, ∀ S : Finset Nat.Primes,
      ‖canonicalEnrichedPrimeCarryDefectProvenanceState M s S‖ ^ 2 =
        finiteSeededTfvdBesselEnergy M s S) := by
  constructor
  · exact genuine_zero_tfvd_seeded_reconstruction_checkpoint
      q hqpos hq1 A hkappa omega homega hs hzero
  · intro M S
    exact
      canonicalEnrichedPrimeCarryDefectProvenanceState_norm_sq_eq_finiteSeededTfvdBesselEnergy
        M s S

end

end CPFormal.Analytic.Cp
