import CPFormal.Analytic.CpC2DirichletJetGpre
import CPFormal.Analytic.CpGenuineGreenKernelInclusion

/-!
# Full-support cofinal synthesis of normalized `G_pre` log atoms

The normalized connected C2 readout at a squarefree semiprime is the fixed
log-Dirichlet atom

`log(p*q) * (p*q)^(-s)`.

A cross-prime camera prefix, however, contains every multiplicative frequency
`p*m` and `q*n`, including the seed (`m = 1`), prime powers, and composite
indices.  Consequently a semiprime-only sum cannot be the exact finite
reindexing of the camera prefix.  The smallest exact synthesis extends the
already certified normalized atom to the full positive multiplicative support.

Every such atom is still read from an active native `G_pre` provenance
coordinate.  The fixed weight

`base / log(base*m)`

removes the logarithmic generator and leaves the ordinary camera term
`base * (base*m)^(-s)`.  Summing these atoms over the two aligned finite
prefixes gives the existing cross-prime camera gap exactly, at every cutoff and
before any zero hypothesis.

This closes `C2GpreNormalizedCofinalIntertwinesCameraGap` for the horizontal
camera-prefix channel.  A final guard records that asking this horizontal
closure to force the critical displacement is still equivalent to the strong
Genuine nonvanishing statement.  The already kernel-checked implication to the
critical displacement applies to the Green flux/provenance closure, not merely
to the horizontal prefix synchronization.
-/

open scoped BigOperators Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-! ## Normalized log atoms as native provenance readouts -/

/-- The cutoff-independent atom left after dividing a connected C2 Richardson
cell by its own support mass. -/
def c2GpreNormalizedLogAtom (n : ℕ) (s : ℂ) : ℂ :=
  natLogDirichletTerm s n

/-- The normalized atom retained at one native cell, with a zero dummy cell
used only to place it in the existing two-point enriched analysis. -/
def c2GpreNormalizedLogAtomAnalysis
    (verticalRatio : ℝ) (S : Finset NativeGpreBoundaryContext)
    (n : ℕ) (s : ℂ) : NativeGpreFiniteTfvdAnalysisCarrier S :=
  c2GprePairEnrichedAnalysis verticalRatio S n 0
    (c2GpreNormalizedLogAtom n s) 0

/-- Any active tag at cell `n` recovers the normalized atom directly from the
`G_pre` value-provenance leg.  No TFVD reconstruction is used. -/
theorem c2GpreNormalizedProvenanceValueReadout_logAtom
    (verticalRatio : ℝ) (S : Finset NativeGpreBoundaryContext)
    (c : ↥S) {n : ℕ} (hn : n ≠ 0)
    (hcell : c.1.cell = n)
    (hactive : c2GpreProvenanceValueCoefficient c.1 ≠ 0)
    (s : ℂ) :
    c2GpreNormalizedProvenanceValueReadout S c
        (c2GpreNormalizedLogAtomAnalysis verticalRatio S n s) =
      c2GpreNormalizedLogAtom n s := by
  exact c2GpreNormalizedProvenanceValueReadout_pair_left
    verticalRatio S c n 0 (c2GpreNormalizedLogAtom n s) 0
      hn hcell hactive

/-- On the squarefree-semiprime locus, the full-support atom is literally the
previously certified normalized connected C2 provenance readout. -/
theorem c2GpreNormalizedLogAtom_eq_connectedC2Readout
    (verticalRatio : ℝ) (S : Finset NativeGpreBoundaryContext)
    {M p q : ℕ} (atlas : C2GpreActiveSpectralAtlas S p q)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    (hpM : p ≤ M) (hqM : q ≤ M) (hpqM : p * q ≤ M)
    (hscale : c2OddCoreCofinalMassScale M p q ≠ 0)
    (s : ℂ) :
    c2GpreNormalizedLogAtom (p * q) s =
      c2OddCoreNormalizedCofinalGpreReadout
        verticalRatio S atlas M s := by
  symm
  exact c2OddCoreNormalizedCofinalGpreReadout_eq_natLogDirichletTerm
    verticalRatio S atlas hp hpodd hq hqodd
      hpM hqM hpqM hscale s

/-! ## Finite camera synthesis -/

/-- Weight that converts the normalized log atom at `base*m` into the ordinary
Dirichlet term of the `base` camera. -/
def c2GpreCameraAtomWeight (base m : ℕ) : ℂ :=
  (base : ℂ) * (Real.log ((base * m : ℕ) : ℝ) : ℂ)⁻¹

/-- One full-support normalized provenance atom with its camera weight. -/
def c2GpreWeightedCameraAtom (base m : ℕ) (s : ℂ) : ℂ :=
  c2GpreCameraAtomWeight base m *
    c2GpreNormalizedLogAtom (base * m) s

/-- For a prime camera and a positive horizontal index, the reciprocal-log
weight removes only the logarithmic generator. -/
theorem c2GpreWeightedCameraAtom_eq_cameraTerm
    (base m : ℕ) (hbase : Nat.Prime base) (hm : 0 < m) (s : ℂ) :
    c2GpreWeightedCameraAtom base m s =
      (base : ℂ) * natDirichletTerm s (base * m) := by
  have hprodNat : 1 < base * m := by
    have hbaseTwo : 2 ≤ base := hbase.two_le
    nlinarith [Nat.mul_le_mul hbaseTwo hm]
  have hprodReal : (1 : ℝ) < ((base * m : ℕ) : ℝ) := by
    exact_mod_cast hprodNat
  have hlogPos : 0 < Real.log ((base * m : ℕ) : ℝ) :=
    Real.log_pos hprodReal
  have hlogReal : Real.log ((base * m : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt hlogPos
  have hlogComplex :
      (Real.log ((base * m : ℕ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hlogReal
  unfold c2GpreWeightedCameraAtom c2GpreCameraAtomWeight
    c2GpreNormalizedLogAtom natLogDirichletTerm
  field_simp [hlogComplex]

/-- Sum of the normalized provenance atoms over the complete positive
multiplicative support of one camera prefix. -/
def c2GpreNormalizedCameraPrefixSynthesis
    (base cutoff : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.range cutoff,
    c2GpreWeightedCameraAtom base (k + 1) s

/-- Exact finite reindexing of the full-support atom synthesis into the usual
weighted Dirichlet prefix of one prime camera. -/
theorem c2GpreNormalizedCameraPrefixSynthesis_eq_weightedPrefix
    (base cutoff : ℕ) (hbase : Nat.Prime base) (s : ℂ) :
    c2GpreNormalizedCameraPrefixSynthesis base cutoff s =
      (base : ℂ) ^ (1 - s) * positiveDirichletPrefix s cutoff := by
  unfold c2GpreNormalizedCameraPrefixSynthesis
  calc
    (∑ k ∈ Finset.range cutoff,
        c2GpreWeightedCameraAtom base (k + 1) s) =
        ∑ k ∈ Finset.range cutoff,
          (base : ℂ) * natDirichletTerm s (base * (k + 1)) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact c2GpreWeightedCameraAtom_eq_cameraTerm
        base (k + 1) hbase (by omega) s
    _ = (base : ℂ) *
        ∑ k ∈ Finset.range cutoff,
          natDirichletTerm s (base * (k + 1)) := by
      rw [Finset.mul_sum]
    _ = (base : ℂ) *
        ∑ k ∈ Finset.range cutoff,
          dirichletTerm s (CPFormal.Genuine.Cp.alignedCenter base k) := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      simp [natDirichletTerm, CPFormal.Genuine.Cp.alignedCenter]
    _ = (base : ℂ) ^ (1 - s) * positiveDirichletPrefix s cutoff := by
      exact p_mul_centerSum_dirichlet_eq_cpow_mul_prefix
        base hbase cutoff s

/-! ## Exact cofinal aggregation and instantiated intertwiner -/

/-- Difference of the two complete normalized provenance syntheses at the
aligned cross-prime cutoffs.  This definition is a finite sum of atoms; it does
not mention the camera-gap expression. -/
def c2GpreNormalizedCofinalSynthesis
    (p q L : ℕ) (s : ℂ) : ℂ :=
  c2GpreNormalizedCameraPrefixSynthesis p
      (crossPrimeAlignedCutoff q L) s -
    c2GpreNormalizedCameraPrefixSynthesis q
      (crossPrimeAlignedCutoff p L) s

/-- The atom synthesis equals the aligned horizontal camera gap at every
finite cofinal level. -/
theorem c2GpreNormalizedCofinalSynthesis_eq_cameraGap
    (p q L : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (s : ℂ) :
    c2GpreNormalizedCofinalSynthesis p q L s =
      c2CrossPrimeCofinalCameraGap p q L s := by
  unfold c2GpreNormalizedCofinalSynthesis c2CrossPrimeCofinalCameraGap
  rw [c2GpreNormalizedCameraPrefixSynthesis_eq_weightedPrefix p
      (crossPrimeAlignedCutoff q L) hp s,
    c2GpreNormalizedCameraPrefixSynthesis_eq_weightedPrefix q
      (crossPrimeAlignedCutoff p L) hq s]

/-- Concrete, non-tautological instance of the previously isolated horizontal
cofinal intertwiner.  Equality holds for every cutoff, hence in particular
eventually. -/
theorem c2GpreNormalizedCofinalSynthesis_intertwinesCameraGap
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (s : ℂ) :
    C2GpreNormalizedCofinalIntertwinesCameraGap
      (fun L : ℕ => c2GpreNormalizedCofinalSynthesis p q L s) p q s := by
  exact Eventually.of_forall fun L =>
    c2GpreNormalizedCofinalSynthesis_eq_cameraGap p q L hp hq s

/-- At a Genuine zero, the concrete atom synthesis closes for the global
oscillatory horizontal-camera reason, not because of the C2 support decay. -/
theorem c2GpreNormalizedCofinalSynthesis_tendsto_zero_of_genuine_zero
    (p q : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
      (fun L : ℕ => c2GpreNormalizedCofinalSynthesis p q L s)
      atTop (nhds 0) := by
  exact normalizedC2GpreProvenanceGap_tendsto_zero_of_genuine_zero
    (fun L : ℕ => c2GpreNormalizedCofinalSynthesis p q L s)
      p q hp hpodd hq hqodd hs hzero
      (c2GpreNormalizedCofinalSynthesis_intertwinesCameraGap
        p q hp hq s)

/-! ## Scope guard for the requested final critical-displacement arrow -/

/-- Claim that closure of this horizontal prefix synthesis, at every Genuine
zero, forces the critical displacement.  The closure premise is already
available at every zero; therefore this claim is not the Green right pillar. -/
def C2GpreHorizontalSynthesisClosureForcesCritical
    (p q : ℕ) : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
    genuineContinuation s = 0 →
    Tendsto
      (fun L : ℕ => c2GpreNormalizedCofinalSynthesis p q L s)
      atTop (nhds 0) →
    criticalDisplacement s.re = 0

/-- Turning horizontal camera-prefix closure into `delta = 0` is exactly the
strong off-critical nonvanishing theorem.  The already proved right pillar is
instead `CrossPrimeAlignedGreenClosure -> delta = 0`. -/
theorem c2GpreHorizontalSynthesisClosureForcesCritical_iff_strongNonvanishing
    (p q : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q) :
    C2GpreHorizontalSynthesisClosureForcesCritical p q ↔
      GenuineStrongNonvanishingInStrip := by
  constructor
  · intro hbridge s hs hoff hzero
    have hclosure :=
      c2GpreNormalizedCofinalSynthesis_tendsto_zero_of_genuine_zero
        p q hp hpodd hq hqodd hs hzero
    have hcritical := hbridge hs hzero hclosure
    apply hoff
    unfold criticalDisplacement at hcritical
    linarith
  · intro hstrong s hs hzero hclosure
    by_contra hcritical
    have hoff : s.re ≠ (1 : ℝ) / 2 := by
      intro hre
      apply hcritical
      unfold criticalDisplacement
      linarith
    exact (hstrong hs hoff) hzero

end

end CPFormal.Analytic.Cp
