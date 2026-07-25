import CPFormal.Analytic.CpGenuineSimpleRootLsbLedgerBessel

/-!
# Exact duality for the simple-root LSB Ledger target

The previous module isolates the desired amplitude estimate

`|T_(M,s,S)(c)| <= L * ||Psi_S(c)||`,

where `Psi_S(c)` is the finite synthesis of critically normalized LSB
velocities and `T` is the root-tangent Green readout.  This file proves that
this is not merely sufficient for a uniform atlas bound: it is exactly the
operator-norm statement for the root-derived provenance atlas.

The canonical Riesz coefficient is

`c_p = R_p * p / (p - 1)`.

With this choice the normalized-LSB synthesis is literally the canonical
root-tangent atlas state, and the scalar test is its squared norm.  Therefore

`SimpleRootLsbLedgerFunctionalBoundAt M s L`

is equivalent to

`0 <= L` and `||X_(M,s,S)|| <= L` for every finite prime atlas `S`.

This is an audit firewall and a unit check.  A scalar Ledger ceiling can close
the route only if it acts as a bounded functional on the full LSB synthesis;
its isolated scalar inequality is not silently promoted to that statement.
-/

open scoped BigOperators ENNReal

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Coordinate formula for a finite normalized-LSB synthesis in the fixed
prime-fiber Hilbert space. -/
@[simp] theorem finiteNormalizedLsbVelocitySynthesis_apply
    (S : Finset Nat.Primes) (coeff : Nat.Primes → ℝ) (p : Nat.Primes) :
    finiteNormalizedLsbVelocitySynthesis S coeff p =
      if p ∈ S then coeff p • primeCriticalCenteredCarryAxis p else 0 := by
  classical
  simp only [finiteNormalizedLsbVelocitySynthesis, lp.coeFn_sum,
    Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single]

/-- Coordinate formula for a finite root-tangent atlas state. -/
@[simp] theorem genuineRootTangentPrimeCarryDefectAtlasState_apply
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) (p : Nat.Primes) :
    genuineRootTangentPrimeCarryDefectAtlasState M s S p =
      if p ∈ S then genuineRootTangentPrimeCarryDefectState p M s else 0 := by
  classical
  simp only [genuineRootTangentPrimeCarryDefectAtlasState, lp.coeFn_sum,
    Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single]

/-- Every active primal LSB axis reads the root-tangent coefficient of its own
camera from the common finite atlas state. -/
theorem inner_globalCarryAxis_rootTangentAtlasState
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes)
    (p : Nat.Primes) (hp : p ∈ S) :
    inner ℝ (primeCriticalCenteredCarryGlobalAxis p)
      (genuineRootTangentPrimeCarryDefectAtlasState M s S) =
        genuineRootTangentGreenBulk p (3 * M) s := by
  rw [inner_primeCriticalCenteredCarryGlobalAxis,
    genuineRootTangentPrimeCarryDefectAtlasState_apply, if_pos hp]
  unfold genuineRootTangentPrimeCarryDefectState
  rw [inner_smul_right, inner_primeCriticalCenteredCarryAxis_dualAxis]
  ring

/-- Exact pairing identity: the root-tangent scalar test is the inner product
between the normalized-LSB synthesis and the root-derived atlas state. -/
theorem inner_finiteNormalizedLsbVelocitySynthesis_rootTangentAtlasState
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes)
    (coeff : Nat.Primes → ℝ) :
    inner ℝ (finiteNormalizedLsbVelocitySynthesis S coeff)
      (genuineRootTangentPrimeCarryDefectAtlasState M s S) =
        simpleRootLsbTangentScalarTest M s S coeff := by
  unfold finiteNormalizedLsbVelocitySynthesis
    simpleRootLsbTangentScalarTest
  simp_rw [inner_sum_left]
  apply Finset.sum_congr rfl
  intro p hp
  rw [lp.inner_single_left, inner_smul_left,
    genuineRootTangentPrimeCarryDefectAtlasState_apply, if_pos hp]
  unfold genuineRootTangentPrimeCarryDefectState
  rw [inner_smul_right, inner_primeCriticalCenteredCarryAxis_dualAxis]
  ring

/-- Coefficient which represents the root atlas state in the primal normalized
LSB axes. -/
def simpleRootLsbRieszCoefficient
    (M : ℕ) (s : ℂ) (p : Nat.Primes) : ℝ :=
  genuineRootTangentGreenBulk p (3 * M) s *
    ((p : ℝ) / ((p : ℝ) - 1))

/-- Locally, the root-derived dual-axis state is the primal LSB axis multiplied
by the Riesz coefficient. -/
theorem genuineRootTangentPrimeCarryDefectState_eq_rieszAxis
    (p : Nat.Primes) (M : ℕ) (s : ℂ) :
    genuineRootTangentPrimeCarryDefectState p M s =
      simpleRootLsbRieszCoefficient M s p •
        primeCriticalCenteredCarryAxis p := by
  unfold genuineRootTangentPrimeCarryDefectState
    simpleRootLsbRieszCoefficient primeCriticalCenteredCarryDualAxis
  rw [smul_smul]
  ring

/-- The normalized-LSB synthesis at the Riesz coefficient is exactly the
finite root-tangent provenance atlas. -/
theorem finiteNormalizedLsbVelocitySynthesis_riesz_eq_rootTangentAtlasState
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) :
    finiteNormalizedLsbVelocitySynthesis S
        (simpleRootLsbRieszCoefficient M s) =
      genuineRootTangentPrimeCarryDefectAtlasState M s S := by
  ext p
  rw [finiteNormalizedLsbVelocitySynthesis_apply,
    genuineRootTangentPrimeCarryDefectAtlasState_apply]
  by_cases hp : p ∈ S
  · rw [if_pos hp, if_pos hp,
      genuineRootTangentPrimeCarryDefectState_eq_rieszAxis]
  · rw [if_neg hp, if_neg hp]

/-- Testing against the Riesz coefficient returns the exact squared norm of
the finite root-tangent atlas. -/
theorem simpleRootLsbTangentScalarTest_riesz_eq_rootTangentAtlasState_norm_sq
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) :
    simpleRootLsbTangentScalarTest M s S
        (simpleRootLsbRieszCoefficient M s) =
      ‖genuineRootTangentPrimeCarryDefectAtlasState M s S‖ ^ 2 := by
  calc
    simpleRootLsbTangentScalarTest M s S
        (simpleRootLsbRieszCoefficient M s) =
      inner ℝ
        (finiteNormalizedLsbVelocitySynthesis S
          (simpleRootLsbRieszCoefficient M s))
        (genuineRootTangentPrimeCarryDefectAtlasState M s S) := by
          rw [inner_finiteNormalizedLsbVelocitySynthesis_rootTangentAtlasState]
    _ = inner ℝ
        (genuineRootTangentPrimeCarryDefectAtlasState M s S)
        (genuineRootTangentPrimeCarryDefectAtlasState M s S) := by
          rw [finiteNormalizedLsbVelocitySynthesis_riesz_eq_rootTangentAtlasState]
    _ = ‖genuineRootTangentPrimeCarryDefectAtlasState M s S‖ ^ 2 :=
      real_inner_self_eq_norm_sq _

/-- Exact norm characterization of the LSB Ledger functional estimate. -/
theorem simpleRootLsbLedgerFunctionalBoundAt_iff_rootTangentAtlas_norm_le
    (M : ℕ) (s : ℂ) (L : ℝ) :
    SimpleRootLsbLedgerFunctionalBoundAt M s L ↔
      0 ≤ L ∧
        ∀ S : Finset Nat.Primes,
          ‖genuineRootTangentPrimeCarryDefectAtlasState M s S‖ ≤ L := by
  constructor
  · intro hbound
    refine ⟨hbound.1, ?_⟩
    intro S
    have htest := hbound.2 S (simpleRootLsbRieszCoefficient M s)
    rw [simpleRootLsbTangentScalarTest_riesz_eq_rootTangentAtlasState_norm_sq,
      finiteNormalizedLsbVelocitySynthesis_riesz_eq_rootTangentAtlasState] at htest
    have hnorm0 :
        0 ≤ ‖genuineRootTangentPrimeCarryDefectAtlasState M s S‖ :=
      norm_nonneg _
    have hsq0 :
        0 ≤ ‖genuineRootTangentPrimeCarryDefectAtlasState M s S‖ ^ 2 :=
      sq_nonneg _
    rw [abs_of_nonneg hsq0] at htest
    nlinarith
  · rintro ⟨hL, hatlas⟩
    refine ⟨hL, ?_⟩
    intro S coeff
    have hinner :=
      abs_real_inner_le_norm
        (finiteNormalizedLsbVelocitySynthesis S coeff)
        (genuineRootTangentPrimeCarryDefectAtlasState M s S)
    rw [inner_finiteNormalizedLsbVelocitySynthesis_rootTangentAtlasState] at hinner
    calc
      |simpleRootLsbTangentScalarTest M s S coeff| ≤
          ‖finiteNormalizedLsbVelocitySynthesis S coeff‖ *
            ‖genuineRootTangentPrimeCarryDefectAtlasState M s S‖ := hinner
      _ ≤ ‖finiteNormalizedLsbVelocitySynthesis S coeff‖ * L :=
        mul_le_mul_of_nonneg_left (hatlas S) (norm_nonneg _)
      _ = L * ‖finiteNormalizedLsbVelocitySynthesis S coeff‖ := by ring

/-- The positive-box LSB functional package is exactly a scalar Ledger package
whose residual bounds the norm—not merely the squared norm—of every finite
root-tangent atlas. -/
theorem exists_positiveBoxLsbLedgerBesselCrosswalk_iff
    (s : ℂ) :
    (∃ hcross : SimpleRootPositiveBoxLsbLedgerBesselCrosswalk s, True) ↔
      ∃ ledger : SimpleRootPositiveBoxScalarLedgerData,
        ∀ S : Finset Nat.Primes,
          ‖genuineRootTangentPrimeCarryDefectAtlasState 1 s S‖ ≤
            ledger.residualLedger := by
  constructor
  · rintro ⟨hcross, _⟩
    refine ⟨hcross.ledger, ?_⟩
    exact
      (simpleRootLsbLedgerFunctionalBoundAt_iff_rootTangentAtlas_norm_le
        1 s hcross.ledger.residualLedger).1 hcross.functional_bound |>.2
  · rintro ⟨ledger, hatlas⟩
    have hfunctional :
        SimpleRootLsbLedgerFunctionalBoundAt 1 s ledger.residualLedger :=
      (simpleRootLsbLedgerFunctionalBoundAt_iff_rootTangentAtlas_norm_le
        1 s ledger.residualLedger).2 ⟨ledger.residual_nonneg, hatlas⟩
    exact ⟨⟨ledger, hfunctional⟩, trivial⟩

/-- The amplitude-level LSB Ledger crosswalk implies the earlier squared-energy
crosswalk.  The implication uses the certified ceiling `13/250 < 1`; no unit
conversion is hidden. -/
def SimpleRootPositiveBoxLsbLedgerBesselCrosswalk.toLedgerMassCrosswalk
    {s : ℂ} (hcross : SimpleRootPositiveBoxLsbLedgerBesselCrosswalk s) :
    SimpleRootPositiveBoxLedgerMassCrosswalk s where
  ledger := hcross.ledger
  atlas_norm_sq_le_residual := by
    intro S
    have hnorm :=
      (simpleRootLsbLedgerFunctionalBoundAt_iff_rootTangentAtlas_norm_le
        1 s hcross.ledger.residualLedger).1 hcross.functional_bound |>.2 S
    have hres0 := hcross.ledger.residual_nonneg
    have hresCeil := hcross.ledger.residual_le_ceiling
    have hceilLtOne : simpleRootPositiveBoxLedgerCeiling < 1 := by
      norm_num [simpleRootPositiveBoxLedgerCeiling]
    have hresLeOne : hcross.ledger.residualLedger ≤ 1 :=
      le_trans hresCeil (le_of_lt hceilLtOne)
    have hnorm0 :
        0 ≤ ‖genuineRootTangentPrimeCarryDefectAtlasState 1 s S‖ :=
      norm_nonneg _
    nlinarith

/-- Consequently the exact LSB functional crosswalk places the simple-root
mass state in the global trace domain through the previously audited route. -/
theorem simpleRootMassVerticalGlobalTraceDomainAt_of_positiveBoxLsbLedgerCrosswalk
    {s : ℂ} (hroot : IsSimpleGenuineZeroInStrip s)
    (hcross : SimpleRootPositiveBoxLsbLedgerBesselCrosswalk s) :
    SimpleRootMassVerticalGlobalTraceDomainAt 1 s hroot :=
  simpleRootMassVerticalGlobalTraceDomainAt_of_positiveBoxLedgerCrosswalk
    hroot hcross.toLedgerMassCrosswalk

end

end CPFormal.Analytic.Cp
