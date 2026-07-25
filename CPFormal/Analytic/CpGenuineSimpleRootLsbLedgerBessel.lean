import CPFormal.Analytic.CpPrimeAdimensionalLsbCrosswalk

/-!
# Bessel extraction from an adimensional-LSB ledger functional

The positive-box scalar ledger bounds one residual amplitude.  The preceding
LSB crosswalk identifies the arithmetic Hilbert directions on which that
residual must act:

* the canonical centered-carry axis is the critically normalized LSB velocity;
* its finite synthesis is an unweighted Bessel family;
* at a simple Genuine root, the enriched Green scalar tests are the tangent
  readouts of the centered-carry Dirichlet transforms.

This module isolates the exact functional estimate that turns a scalar ledger
ceiling `L` into the desired uniform Bessel constant `L^2`.  The estimate is
not declared from `ledger_strict`: it says that the root-tangent readout is a
bounded functional on every finite normalized-LSB synthesis.  Once that one
semantic crosswalk is supplied, the existing Bessel machinery forces critical
localization.
-/

open scoped BigOperators ENNReal

namespace CPFormal.Analytic.Cp

noncomputable section

/-- The critically normalized LSB velocity is the primal centered-carry axis.
The raw adimensional LSB velocity is its canonical dual. -/
theorem primeCriticalCenteredCarryAxis_apply_eq_normalizedLsbIncrement
    (p : Nat.Primes) (a : Fin p.1) :
    primeCriticalCenteredCarryAxis p a =
      (((p : ℝ) - 1) / (p : ℝ)) * primeAdimensionalLsbIncrement p a := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
  rw [primeCriticalCenteredCarryAxis_apply,
    primeCarryDefectAxisCoefficient_eq_inv,
    primeCenteredCarryDefect_eq_scale_mul_lsbIncrement]
  field_simp [hp0]

/-- Finite synthesis of the normalized LSB velocities, embedded in the fixed
global prime-fiber Hilbert space. -/
def finiteNormalizedLsbVelocitySynthesis
    (S : Finset Nat.Primes) (coeff : Nat.Primes → ℝ) :
    PrimeCarryDefectGlobalHilbert :=
  ∑ p ∈ S,
    lp.single 2 p (coeff p • primeCriticalCenteredCarryAxis p)

/-- The normalized LSB synthesis is an unweighted Bessel family. -/
theorem finiteNormalizedLsbVelocitySynthesis_norm_sq_le
    (S : Finset Nat.Primes) (coeff : Nat.Primes → ℝ) :
    ‖finiteNormalizedLsbVelocitySynthesis S coeff‖ ^ 2 ≤
      ∑ p ∈ S, (coeff p) ^ 2 := by
  have hraw :=
    lp.norm_sum_single
      (E := fun p : Nat.Primes => PrimeCarryResidueHilbert p)
      (p := (2 : ℝ≥0∞)) (by norm_num)
      (fun p : Nat.Primes => coeff p • primeCriticalCenteredCarryAxis p) S
  rw [show ‖finiteNormalizedLsbVelocitySynthesis S coeff‖ ^ 2 =
      ∑ p ∈ S, ‖coeff p • primeCriticalCenteredCarryAxis p‖ ^ 2 by
        simpa [finiteNormalizedLsbVelocitySynthesis] using hraw]
  apply Finset.sum_le_sum
  intro p hp
  rw [norm_smul, Real.norm_eq_abs]
  have haxis := primeCriticalCenteredCarryAxis_norm_le_one p
  have habs0 : 0 ≤ |coeff p| := abs_nonneg _
  have hnorm0 : 0 ≤ ‖primeCriticalCenteredCarryAxis p‖ := norm_nonneg _
  have hmul :
      |coeff p| * ‖primeCriticalCenteredCarryAxis p‖ ≤ |coeff p| := by
    simpa using mul_le_mul_of_nonneg_left haxis habs0
  have hleft0 :
      0 ≤ |coeff p| * ‖primeCriticalCenteredCarryAxis p‖ :=
    mul_nonneg habs0 hnorm0
  have hsq :
      (|coeff p| * ‖primeCriticalCenteredCarryAxis p‖) ^ 2 ≤
        |coeff p| ^ 2 :=
    (sq_le_sq₀ hleft0 habs0).2 hmul
  simpa [sq_abs] using hsq

/-- Scalar test reconstructed from the simple-root tangents of the centered
carry transforms.  The cutoff `3M` matches the three Green edges encoded by
one enriched TFVD block. -/
def simpleRootLsbTangentScalarTest
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes)
    (coeff : Nat.Primes → ℝ) : ℝ :=
  ∑ p ∈ S, coeff p * genuineRootTangentGreenBulk p (3 * M) s

/-- At a simple Genuine zero, the LSB tangent test is exactly the existing
enriched `G_pre` log-jet Green scalar test. -/
theorem simpleRootLsbTangentScalarTest_eq_canonical
    (M : ℕ) (S : Finset Nat.Primes) (coeff : Nat.Primes → ℝ)
    {s : ℂ} (hroot : IsSimpleGenuineZeroInStrip s) :
    simpleRootLsbTangentScalarTest M s S coeff =
      canonicalEnrichedGpreLogJetGreenScalarTest M s S coeff := by
  unfold simpleRootLsbTangentScalarTest
    canonicalEnrichedGpreLogJetGreenScalarTest
  apply Finset.sum_congr rfl
  intro p hp
  rw [genuineRootTangentGreenBulk_eq_of_simple_zero p (3 * M) hroot,
    finiteEnrichedNativeGpreLogJetGreenBulkReadout_eq
      p M (by norm_num) (fun _ => 1) (by intro m; norm_num) s]

/-- The exact amplitude-level statement a scalar Ledger must provide.

`L` bounds the root-tangent readout as a functional on the arithmetic Hilbert
synthesis of normalized LSB velocities.  This is stronger than a bound on one
fixed scalar residual, but weaker and more structural than postulating the
final prime-atlas norm directly. -/
def SimpleRootLsbLedgerFunctionalBoundAt
    (M : ℕ) (s : ℂ) (L : ℝ) : Prop :=
  0 ≤ L ∧
    ∀ (S : Finset Nat.Primes) (coeff : Nat.Primes → ℝ),
      |simpleRootLsbTangentScalarTest M s S coeff| ≤
        L * ‖finiteNormalizedLsbVelocitySynthesis S coeff‖

/-- A Ledger functional ceiling `L` yields the unweighted scalar Bessel
estimate with the explicit constant `L^2`. -/
theorem simpleRootLsbTangentScalarTest_sq_le_of_ledgerFunctionalBound
    {M : ℕ} {s : ℂ} {L : ℝ}
    (hbound : SimpleRootLsbLedgerFunctionalBoundAt M s L)
    (S : Finset Nat.Primes) (coeff : Nat.Primes → ℝ) :
    (simpleRootLsbTangentScalarTest M s S coeff) ^ 2 ≤
      L ^ 2 * ∑ p ∈ S, (coeff p) ^ 2 := by
  have htest := hbound.2 S coeff
  have hsynth := finiteNormalizedLsbVelocitySynthesis_norm_sq_le S coeff
  have habs0 :
      0 ≤ |simpleRootLsbTangentScalarTest M s S coeff| := abs_nonneg _
  have hright0 :
      0 ≤ L * ‖finiteNormalizedLsbVelocitySynthesis S coeff‖ :=
    mul_nonneg hbound.1 (norm_nonneg _)
  have hsq :
      |simpleRootLsbTangentScalarTest M s S coeff| ^ 2 ≤
        (L * ‖finiteNormalizedLsbVelocitySynthesis S coeff‖) ^ 2 :=
    (sq_le_sq₀ habs0 hright0).2 htest
  calc
    (simpleRootLsbTangentScalarTest M s S coeff) ^ 2 =
        |simpleRootLsbTangentScalarTest M s S coeff| ^ 2 :=
      (sq_abs _).symm
    _ ≤ (L * ‖finiteNormalizedLsbVelocitySynthesis S coeff‖) ^ 2 := hsq
    _ = L ^ 2 * ‖finiteNormalizedLsbVelocitySynthesis S coeff‖ ^ 2 := by ring
    _ ≤ L ^ 2 * ∑ p ∈ S, (coeff p) ^ 2 :=
      mul_le_mul_of_nonneg_left hsynth (sq_nonneg L)

/-- Audit-only positive-box package: the external scalar ledger data together
with the missing statement that the ledger acts boundedly on every normalized
LSB synthesis. -/
structure SimpleRootPositiveBoxLsbLedgerBesselCrosswalk (s : ℂ) where
  ledger : SimpleRootPositiveBoxScalarLedgerData
  functional_bound :
    SimpleRootLsbLedgerFunctionalBoundAt 1 s ledger.residualLedger

/-- The positive-box ceiling gives a completely explicit Bessel constant.
The ledger is an amplitude bound, hence the quadratic constant is
`(13 / 250)^2`. -/
theorem canonicalScalarTestsBounded_of_positiveBoxLsbLedgerCrosswalk
    {s : ℂ} (hroot : IsSimpleGenuineZeroInStrip s)
    (hcross : SimpleRootPositiveBoxLsbLedgerBesselCrosswalk s) :
    CanonicalEnrichedGpreLogJetGreenScalarTestsBounded 1 s := by
  let C : ℝ := simpleRootPositiveBoxLedgerCeiling ^ 2
  have hceiling0 : 0 ≤ simpleRootPositiveBoxLedgerCeiling :=
    simpleRootPositiveBoxLedgerCeiling_nonneg
  have hresSq :
      hcross.ledger.residualLedger ^ 2 ≤ C := by
    dsimp [C]
    exact
      (sq_le_sq₀ hcross.ledger.residual_nonneg hceiling0).2
        hcross.ledger.residual_le_ceiling
  refine ⟨C, sq_nonneg _, ?_⟩
  intro S coeff
  have hrootBound :=
    simpleRootLsbTangentScalarTest_sq_le_of_ledgerFunctionalBound
      hcross.functional_bound S coeff
  have hsum0 : 0 ≤ ∑ p ∈ S, (coeff p) ^ 2 :=
    Finset.sum_nonneg fun p hp => sq_nonneg _
  rw [← simpleRootLsbTangentScalarTest_eq_canonical
    1 S coeff hroot]
  exact le_trans hrootBound
    (mul_le_mul_of_nonneg_right hresSq hsum0)

/-- Once the LSB-functional crosswalk is supplied, the Bessel estimate forces
the simple root onto the half-abscissa. -/
theorem criticalDisplacement_eq_zero_of_simpleRoot_positiveBoxLsbLedgerCrosswalk
    {s : ℂ} (hroot : IsSimpleGenuineZeroInStrip s)
    (hcross : SimpleRootPositiveBoxLsbLedgerBesselCrosswalk s) :
    criticalDisplacement s.re = 0 := by
  exact
    (canonicalEnrichedGpreLogJetGreenScalarTestsBounded_iff
      1 (by norm_num) hroot.1).1
      (canonicalScalarTestsBounded_of_positiveBoxLsbLedgerCrosswalk
        hroot hcross)

/-- Since the selected positive box is strictly off-critical, the functional
Ledger-to-LSB crosswalk excludes a simple Genuine zero throughout that box. -/
theorem no_simpleGenuineZeroIn_positiveBox_of_lsbLedgerBesselCrosswalk
    {s : ℂ} (hsBox : s ∈ simpleRootLedgerPositiveBox)
    (hroot : IsSimpleGenuineZeroInStrip s)
    (hcross : SimpleRootPositiveBoxLsbLedgerBesselCrosswalk s) :
    False := by
  have hpos : 0 < criticalDisplacement s.re :=
    criticalDisplacement_pos_of_mem_simpleRootLedgerPositiveBox hsBox
  have hzero : criticalDisplacement s.re = 0 :=
    criticalDisplacement_eq_zero_of_simpleRoot_positiveBoxLsbLedgerCrosswalk
      hroot hcross
  linarith

end

end CPFormal.Analytic.Cp
