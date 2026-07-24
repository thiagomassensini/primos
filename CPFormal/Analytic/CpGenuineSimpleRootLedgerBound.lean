import CPFormal.Analytic.CpGenuineSimpleRootCarryState

/-!
# Audit-only positive-box ledger bound for multiplicity-one roots

The positive-box ledger currently lives in the separate Lean project
`formalizacao_C2`, in
`LeanC2/AuditContinuedQuartetPositiveBoxInterval.lean`.  That project uses a
different Mathlib revision, so this `CPFormal` module does not import it as a
library dependency.  Instead, it records the exact scalar output needed from
that audit:

* the residual ledger is nonnegative;
* it is bounded above by the rational ceiling `13 / 250`;
* it is strictly below the positive-box sector margin.

The external theorem `PositiveBoxLedgerBounds.ledger_strict` supplies the last
comparison once its q/horizontal data are available.  The rational ceiling
itself is supplied there by `positiveBoxLedger_left_le`.

The genuinely new bridge would have to show that every finite prime-atlas norm
of the state reconstructed from a simple Genuine root is bounded by that same
residual ledger.  This field is kept explicit below.  Once supplied, the
existing root-tangent/Bessel machinery proves the global trace domain and
critical localization without any additional analytic estimate.

Nothing in this module declares the bridge from scalar ledger to prime-atlas
energy.  In particular, `ledger_strict` alone is not treated as a Hilbert norm
bound.
-/

open scoped BigOperators ENNReal

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Local mirror of the real lower edge of the audit-only positive box. -/
def simpleRootLedgerPositiveBoxSigmaMin : ℝ :=
  (21 : ℝ) / 25

/-- Local mirror of the real upper edge of the audit-only positive box. -/
def simpleRootLedgerPositiveBoxSigmaMax : ℝ :=
  (43 : ℝ) / 50

/-- Local mirror of the imaginary lower edge of the refined positive box. -/
def simpleRootLedgerPositiveBoxTMin : ℝ :=
  (1641 : ℝ) / 50

/-- Local mirror of the imaginary upper edge of the refined positive box. -/
def simpleRootLedgerPositiveBoxTMax : ℝ :=
  (1643 : ℝ) / 50

/-- Audit-only copy of the positive box used by the external ledger project. -/
def simpleRootLedgerPositiveBox : Set ℂ :=
  fun s =>
    simpleRootLedgerPositiveBoxSigmaMin ≤ s.re ∧
      s.re ≤ simpleRootLedgerPositiveBoxSigmaMax ∧
      simpleRootLedgerPositiveBoxTMin ≤ s.im ∧
      s.im ≤ simpleRootLedgerPositiveBoxTMax

/-- The whole audit box lies strictly to the right of the half-abscissa. -/
theorem criticalDisplacement_pos_of_mem_simpleRootLedgerPositiveBox
    {s : ℂ} (hs : s ∈ simpleRootLedgerPositiveBox) :
    0 < criticalDisplacement s.re := by
  change simpleRootLedgerPositiveBoxSigmaMin ≤ s.re ∧
      s.re ≤ simpleRootLedgerPositiveBoxSigmaMax ∧
      simpleRootLedgerPositiveBoxTMin ≤ s.im ∧
      s.im ≤ simpleRootLedgerPositiveBoxTMax at hs
  rcases hs with ⟨hre, _⟩
  norm_num [simpleRootLedgerPositiveBoxSigmaMin, criticalDisplacement] at hre ⊢
  linarith

/-- Rational ceiling proved for the left side of the external positive-box
scalar ledger. -/
def simpleRootPositiveBoxLedgerCeiling : ℝ :=
  (13 : ℝ) / 250

/-- The external rational ceiling is finite and nonnegative. -/
theorem simpleRootPositiveBoxLedgerCeiling_nonneg :
    0 ≤ simpleRootPositiveBoxLedgerCeiling := by
  norm_num [simpleRootPositiveBoxLedgerCeiling]

/-- Scalar information exported by the positive-box ledger audit.

The strict comparison is retained because it is the physical credit/debt
ledger.  The separate `residual_le_ceiling` field records the actual finite
upper bound used by the Hilbert argument.  This is a data structure rather
than a proposition because it stores the two real ledger values. -/
structure SimpleRootPositiveBoxScalarLedgerData where
  residualLedger : ℝ
  sectorMargin : ℝ
  residual_nonneg : 0 ≤ residualLedger
  residual_le_ceiling :
    residualLedger ≤ simpleRootPositiveBoxLedgerCeiling
  ledger_strict : residualLedger < sectorMargin

/-- The missing semantic crosswalk from the scalar positive-box ledger to the
prime-atlas energy reconstructed from the root tangent.

Only `atlas_norm_sq_le_residual` is not supplied by the scalar ledger theorem
itself.  It must be proved from the bracket conservation/provenance identity,
not postulated as a global instance. -/
structure SimpleRootPositiveBoxLedgerMassCrosswalk (s : ℂ) where
  ledger : SimpleRootPositiveBoxScalarLedgerData
  atlas_norm_sq_le_residual :
    ∀ S : Finset Nat.Primes,
      ‖genuineRootTangentPrimeCarryDefectAtlasState 1 s S‖ ^ 2 ≤
        ledger.residualLedger

/-- A ledger-to-mass crosswalk immediately supplies a uniform bound for all
finite root-tangent prime atlases, with the explicit constant `13 / 250`. -/
theorem genuineRootTangentAtlasStatesBounded_of_positiveBoxLedgerCrosswalk
    {s : ℂ} (hcross : SimpleRootPositiveBoxLedgerMassCrosswalk s) :
    GenuineRootTangentPrimeCarryDefectAtlasStatesBounded 1 s := by
  refine ⟨simpleRootPositiveBoxLedgerCeiling, ?_⟩
  intro S
  exact le_trans (hcross.atlas_norm_sq_le_residual S)
    hcross.ledger.residual_le_ceiling

/-- For a multiplicity-one Genuine zero, the same crosswalk forces critical
localization. -/
theorem criticalDisplacement_eq_zero_of_simpleRoot_positiveBoxLedgerCrosswalk
    {s : ℂ} (hroot : IsSimpleGenuineZeroInStrip s)
    (hcross : SimpleRootPositiveBoxLedgerMassCrosswalk s) :
    criticalDisplacement s.re = 0 := by
  have hbounded :
      GenuineRootTangentPrimeCarryDefectAtlasStatesBounded 1 s :=
    genuineRootTangentAtlasStatesBounded_of_positiveBoxLedgerCrosswalk hcross
  exact
    (genuineRootTangentPrimeCarryDefectAtlasStatesBounded_iff
      1 (by norm_num) hroot.1 hroot.2.1 hroot.2.2
      (deriv_genuineContinuation_reflectedParameter_ne_zero_of_simple_zero
        hroot.1 hroot.2.1 hroot.2.2)).1 hbounded

/-- The ledger crosswalk places the global mass state of a simple root in the
simultaneous primewise vertical-trace domain. -/
theorem simpleRootMassVerticalGlobalTraceDomainAt_of_positiveBoxLedgerCrosswalk
    {s : ℂ} (hroot : IsSimpleGenuineZeroInStrip s)
    (hcross : SimpleRootPositiveBoxLedgerMassCrosswalk s) :
    SimpleRootMassVerticalGlobalTraceDomainAt 1 s hroot := by
  exact
    (simpleRootMassVerticalGlobalTraceDomainAt_iff
      1 (by norm_num) hroot).2
      (criticalDisplacement_eq_zero_of_simpleRoot_positiveBoxLedgerCrosswalk
        hroot hcross)

/-- Since the selected positive box is strictly off-critical, no simple Genuine
zero in that box can satisfy the missing ledger-to-atlas crosswalk.  This is the
audit firewall against silently identifying scalar residual dominance with
uniform Hilbert control. -/
theorem no_simpleGenuineZeroIn_positiveBox_of_ledgerMassCrosswalk
    {s : ℂ} (hsBox : s ∈ simpleRootLedgerPositiveBox)
    (hroot : IsSimpleGenuineZeroInStrip s)
    (hcross : SimpleRootPositiveBoxLedgerMassCrosswalk s) :
    False := by
  have hpos : 0 < criticalDisplacement s.re :=
    criticalDisplacement_pos_of_mem_simpleRootLedgerPositiveBox hsBox
  have hzero : criticalDisplacement s.re = 0 :=
    criticalDisplacement_eq_zero_of_simpleRoot_positiveBoxLedgerCrosswalk
      hroot hcross
  linarith

end

end CPFormal.Analytic.Cp
