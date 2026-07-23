import CPFormal.Analytic.CpC2OddCorePushforwardTfvd
import CPFormal.Analytic.CpFiniteLogJetCommutator
import CPFormal.Analytic.CpFiniteSeededTfvdGreenIdentity
import CPFormal.Analytic.CpNativeGpreTfvdAnalysis

/-!
# Lossless C2 log-jet lift into the enriched `G_pre` analysis

The concrete connected C2 cell already lands in a scalar multiple of a
finite sum of consecutive log-Dirichlet gradients.  This module keeps that
log-jet sum as a finitely supported edge state and sends the whole state
through the existing enriched TFVD--`G_pre` analysis.  The connected C2
coefficient remains an external scalar in the final factorization.

This is the forward construction suggested by the provenance canon:

* no sum over the arithmetic provenance coordinates is performed;
* the same native edge state feeds the TFVD bracket/trace and `G_pre` legs;
* the existing TFVD reconstruction is a continuous left inverse;
* the original scalar log-Dirichlet vertex is recovered only after the
  enriched state has been formed.

Thus the log-jet prefix used by the C2 readout has a lossless realization
through the enriched carrier at every finite provenance atlas.  The current
left inverse reconstructs it through the TFVD leg; no theorem below says that
the provenance legs detect the external connected coefficient.  In
particular, this does not yet identify any coordinate with the weighted
canonical `same-s` Green provenance, and it does not assume a Genuine zero or
an off-critical nonvanishing statement.
-/

open scoped BigOperators

namespace CPFormal.Analytic.Cp

noncomputable section

/-- The first `N` native log-jet edges, kept as a finitely supported state. -/
def c2LogJetPrefixCore (s : ℂ) (N : ℕ) :
    NativeGpreComplexEdgeCore :=
  Finsupp.onFinset (Finset.range N)
    (fun n ↦
      if n < N then positiveLogDirichletGradient s n else 0)
    (by
      intro n hn
      by_contra hmem
      have hnlt : ¬n < N := by
        simpa only [Finset.mem_range, not_false_eq_true] using hmem
      simp [hnlt] at hn)

@[simp] theorem c2LogJetPrefixCore_apply
    (s : ℂ) (N n : ℕ) :
    c2LogJetPrefixCore s N n =
      if n < N then positiveLogDirichletGradient s n else 0 := by
  classical
  simp [c2LogJetPrefixCore]

/-- Finite synthesis on the first `N` coordinates of the vertical Hilbert
state.  It is used only after the provenance-enriched analysis. -/
def carryVerticalFinitePrefixSum (N : ℕ) :
    CarryVerticalL2 →L[ℂ] ℂ :=
  ∑ n ∈ Finset.range N, carryVerticalL2Eval n

@[simp] theorem carryVerticalFinitePrefixSum_apply
    (N : ℕ) (x : CarryVerticalL2) :
    carryVerticalFinitePrefixSum N x =
      ∑ n ∈ Finset.range N, x n := by
  simp [carryVerticalFinitePrefixSum]

/-- The finitely supported prefix synthesizes to the native
log-Dirichlet vertex. -/
theorem c2LogJetPrefixCore_sum_eq
    (s : ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N, c2LogJetPrefixCore s N n) =
      positiveLogDirichletValue s N := by
  rw [positiveLogDirichletValue_eq_sum_range_gradient]
  apply Finset.sum_congr rfl
  intro n hn
  rw [c2LogJetPrefixCore_apply]
  simp only [Finset.mem_range] at hn
  simp [hn]

/-!
## Exact product crosswalk
-/

/--
The log-Dirichlet vertex at `p*q` is exactly two block-local seed terms plus
the two finite log-jet commutator boundaries.  No primality, strip condition,
or Genuine zero is used.
-/
theorem positiveLogDirichletValue_product_eq_logScales_add_commutators
    {p q : ℕ} (hp : p ≠ 0) (hq : q ≠ 0) (s : ℂ) :
    positiveLogDirichletValue s (p * q - 1) =
      cpLogScaleCoefficient p s +
        cpLogScaleCoefficient q s +
          finiteCpLogJetCommutator p (q - 1) s +
            finiteCpLogJetCommutator q (p - 1) s := by
  have hpqPred : p * q - 1 + 1 = p * q :=
    Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hp hq))
  have hpPred : p - 1 + 1 = p :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hp)
  have hqPred : q - 1 + 1 = q :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hq)
  rw [
    positiveLogDirichletValue_eq_natLogDirichletTerm,
    hpqPred,
    natLogDirichletTerm_mul p q hp hq,
    finiteCpLogJetCommutator_eq_boundary p (q - 1) hp,
    finiteCpLogJetCommutator_eq_boundary q (p - 1) hq]
  simp_rw [positiveDirichletValue_eq_natDirichletTerm]
  rw [hpPred, hqPred]
  have hone : natDirichletTerm s 1 = 1 := by
    simp [natDirichletTerm, dirichletTerm]
  simp only [Nat.zero_add, hone]
  unfold natLogDirichletTerm cpLogScaleCoefficient
  ring

/-!
## `same-s` covariance under the prime block
-/

/-- The native local wedge is definitionally the canonical `same-s` cell
already used by the finite Green provenance.  The abbreviation only swaps
the argument order to match the block formulas below. -/
abbrev canonicalLogJetSameSEdgeWedge (s : ℂ) (n : ℕ) : ℂ :=
  canonicalSameSEdgeBoundaryWedge n s

/-- The same wedge after applying the `p`-block to both fields. -/
def cpLogJetSameSBlockWedge (p : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  sameSEdgeBoundaryWedge
    (cpBlockGradient p s n)
    (cpBlockGradient p s (n + 1))
    (cpLogBlockGradient p s n)
    (cpLogBlockGradient p s (n + 1))

/--
The logarithmic Jordan shear cancels exactly in the `same-s` determinant.
Only the square of the ordinary block eigenvalue survives.
-/
theorem cpLogJetSameSBlockWedge_eq_eigenvalue_sq_mul
    (p : ℕ) (hp : p ≠ 0) (s : ℂ) (n : ℕ) :
    cpLogJetSameSBlockWedge p s n =
      (natDirichletTerm s p) ^ 2 *
        canonicalLogJetSameSEdgeWedge s n := by
  unfold cpLogJetSameSBlockWedge canonicalLogJetSameSEdgeWedge
    canonicalSameSEdgeBoundaryWedge sameSEdgeBoundaryWedge
  rw [
    cpBlockGradient_eq_eigenvalue_mul,
    cpBlockGradient_eq_eigenvalue_mul,
    cpLogBlockGradient_eq_eigenvalue_mul_logJet_add_logScale p hp,
    cpLogBlockGradient_eq_eigenvalue_mul_logJet_add_logScale p hp]
  ring

/-- The log-block after removing the same phase and critical scale used on
the ordinary block. -/
def phaseNormalizedCpLogBlockGradient
    (p : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  cpPhaseNormalizer p s * cpLogBlockGradient p s n

/-- The `same-s` wedge after normalizing both the ordinary and logarithmic
block legs. -/
def phaseNormalizedCpLogJetSameSBlockWedge
    (p : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  sameSEdgeBoundaryWedge
    (phaseNormalizedCpBlockGradient p s n)
    (phaseNormalizedCpBlockGradient p s (n + 1))
    (phaseNormalizedCpLogBlockGradient p s n)
    (phaseNormalizedCpLogBlockGradient p s (n + 1))

/--
After phase normalization, the local wedge is multiplied by the real radial
factor `p^(-2*delta)`.  This is a covariance law for one camera; it does not
assert agreement between distinct cameras.
-/
theorem phaseNormalizedCpLogJetSameSBlockWedge_eq_radial_sq_mul
    (p : ℕ) (hp : Nat.Prime p) (s : ℂ) (n : ℕ) :
    phaseNormalizedCpLogJetSameSBlockWedge p s n =
      ((((p : ℝ) ^ (-criticalDisplacement s.re) : ℝ) : ℂ) ^ 2) *
        canonicalLogJetSameSEdgeWedge s n := by
  let k := cpPhaseNormalizer p s
  calc
    phaseNormalizedCpLogJetSameSBlockWedge p s n =
        k ^ 2 * cpLogJetSameSBlockWedge p s n := by
      unfold phaseNormalizedCpLogJetSameSBlockWedge
        phaseNormalizedCpBlockGradient
        phaseNormalizedCpLogBlockGradient
        cpLogJetSameSBlockWedge sameSEdgeBoundaryWedge
      dsimp [k]
      ring
    _ = k ^ 2 * ((natDirichletTerm s p) ^ 2 *
        canonicalLogJetSameSEdgeWedge s n) := by
      rw [cpLogJetSameSBlockWedge_eq_eigenvalue_sq_mul
        p hp.ne_zero s n]
    _ = (k * natDirichletTerm s p) ^ 2 *
        canonicalLogJetSameSEdgeWedge s n := by ring
    _ = ((((p : ℝ) ^ (-criticalDisplacement s.re) : ℝ) : ℂ) ^ 2) *
        canonicalLogJetSameSEdgeWedge s n := by
      rw [cpPhaseNormalizer_mul_eigenvalue p hp s]

/-!
## Dyadic decay guard
-/

/-- Named connected coefficient multiplying the fixed semiprime log-jet
vertex in the concrete Richardson cell. -/
def c2OddCoreConnectedRichardsonDefect
    (M p q : ℕ) : ℚ :=
  (1 / 2 : ℚ) *
    c2OddCoreFourScaleDefect M p *
      c2OddCoreFourScaleDefect M q

/-- Each concrete marginal defect is halved when the dyadic cutoff doubles. -/
theorem c2OddCoreFourScaleDefect_two_mul_eq_half
    {M m : ℕ} (hm : 0 < m) (hmM : m ≤ M) :
    c2OddCoreFourScaleDefect (2 * M) m =
      (1 / 2 : ℚ) * c2OddCoreFourScaleDefect M m := by
  unfold c2OddCoreFourScaleDefect
  have hcutoff : 4 * (2 * M) = 8 * M := by ring
  rw [hcutoff,
    CPFormal.Carry.C2.oddCoreTruncatedMass_eight_mul_eq hm hmM]
  ring

/-- The connected coefficient therefore loses exactly a factor `1/4` at
each dyadic scale doubling. -/
theorem c2OddCoreConnectedRichardsonDefect_two_mul_eq_quarter
    {M p q : ℕ}
    (hp : 0 < p) (hq : 0 < q)
    (hpM : p ≤ M) (hqM : q ≤ M) :
    c2OddCoreConnectedRichardsonDefect (2 * M) p q =
      (1 / 4 : ℚ) *
        c2OddCoreConnectedRichardsonDefect M p q := by
  unfold c2OddCoreConnectedRichardsonDefect
  rw [
    c2OddCoreFourScaleDefect_two_mul_eq_half hp hpM,
    c2OddCoreFourScaleDefect_two_mul_eq_half hq hqM]
  ring

/-- The same scalar recovery after the canonical inclusion into `ell^2`. -/
theorem carryVerticalFinitePrefixSum_c2LogJetPrefix
    (s : ℂ) (N : ℕ) :
    carryVerticalFinitePrefixSum N
        (nativeGpreCanonicalVerticalRealization
          (c2LogJetPrefixCore s N)) =
      positiveLogDirichletValue s N := by
  rw [carryVerticalFinitePrefixSum_apply]
  simp only [nativeGpreCanonicalVerticalRealization_apply]
  exact c2LogJetPrefixCore_sum_eq s N

/-- The log-jet prefix used by the C2 readout, in the enriched finite-atlas
analysis. -/
def c2LogJetPrefixEnrichedAnalysis
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (s : ℂ) (N : ℕ) :
    NativeGpreFiniteTfvdAnalysisCarrier S :=
  nativeGpreFiniteTfvdAnalysis q S
    (nativeGpreCanonicalVerticalRealization
      (c2LogJetPrefixCore s N))

/-- A readout on enriched data obtained by first using the canonical TFVD
left inverse and only then summing the requested finite prefix. -/
def c2LogJetPrefixEnrichedReadout
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (N : ℕ) :
    NativeGpreFiniteTfvdAnalysisCarrier S →L[ℂ] ℂ :=
  (carryVerticalFinitePrefixSum N).comp
    (nativeGpreFiniteTfvdReconstruction q hq0 hq1 S)

/-- The enriched analysis reconstructs the complete log-jet prefix used by
the C2 readout. -/
theorem c2LogJetPrefixEnrichedAnalysis_reconstruction
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (s : ℂ) (N : ℕ) :
    nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S
        (c2LogJetPrefixEnrichedAnalysis q S s N) =
      nativeGpreCanonicalVerticalRealization
        (c2LogJetPrefixCore s N) := by
  exact nativeGpreFiniteTfvdReconstruction_analysis
    q hqpos hq1 S
      (nativeGpreCanonicalVerticalRealization
        (c2LogJetPrefixCore s N))

/-- Scalar synthesis is recovered from the enriched state.  The state also
contains provenance coordinates, although the current reconstruction map
uses only its TFVD leg. -/
theorem c2LogJetPrefixEnrichedReadout_analysis
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (s : ℂ) (N : ℕ) :
    c2LogJetPrefixEnrichedReadout q hqpos.le hq1 S N
        (c2LogJetPrefixEnrichedAnalysis q S s N) =
      positiveLogDirichletValue s N := by
  rw [c2LogJetPrefixEnrichedReadout]
  simp only [ContinuousLinearMap.comp_apply]
  rw [c2LogJetPrefixEnrichedAnalysis_reconstruction
    q hqpos hq1 S s N]
  exact carryVerticalFinitePrefixSum_c2LogJetPrefix s N

/-- Every retained provenance coordinate is read from the same unsynthesized
log-jet prefix state. -/
theorem c2LogJetPrefixEnrichedAnalysis_provenance_value
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (s : ℂ) (N : ℕ) (c : ↥S) :
    (c2LogJetPrefixEnrichedAnalysis q S s N).2.1 c =
      c2LogJetPrefixCore s N c.1.cell *
        (nativeGpreTowerCoordinateCoefficient
          (c.1.withRole .value) : ℂ) := by
  simp [c2LogJetPrefixEnrichedAnalysis,
    nativeGpreFiniteTfvdAnalysis_apply]

/-- The number-flux coordinate remains `j` times the value coordinate on the
lifted C2 state. -/
theorem c2LogJetPrefixEnrichedAnalysis_numberFlux_eq_level_mul_value
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (s : ℂ) (N : ℕ) (c : ↥S) :
    (c2LogJetPrefixEnrichedAnalysis q S s N).2.2 c =
      (c.1.towerLevel.val : ℂ) *
        (c2LogJetPrefixEnrichedAnalysis q S s N).2.1 c := by
  change
    nativeGpreFiniteContinuousBoundaryNumberFluxLift S
        (nativeGpreCanonicalVerticalRealization
          (c2LogJetPrefixCore s N)) c =
      (c.1.towerLevel.val : ℂ) *
        nativeGpreFiniteContinuousBoundaryValueLift S
          (nativeGpreCanonicalVerticalRealization
            (c2LogJetPrefixCore s N)) c
  rw [
    nativeGpreFiniteContinuousBoundaryNumberFluxLift_canonical,
    nativeGpreFiniteContinuousBoundaryValueLift_canonical]
  exact nativeGpreFiniteBoundaryNumberFlux_eq_level_mul_value
    S (c2LogJetPrefixCore s N) c

/--
The concrete semiprime Richardson scalar now factors through the enriched
TFVD--`G_pre` analysis.  The connected coefficient stays outside the
analysis.  The argument supplied to the scalar readout retains the complete
finite log-jet prefix and also populates every selected provenance
coordinate, but this theorem does not use those coordinates to recover the
coefficient.
-/
theorem
    c2OddCoreLogCoefficient_richardson_eq_defect_mul_enrichedGpreReadout
    {M p q : ℕ}
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q) (hpq : p ≠ q)
    (hpM : p ≤ M) (hqM : q ≤ M) (hpqM : p * q ≤ M)
    (s : ℂ)
    (verticalRatio : ℝ) (hvrpos : 0 < verticalRatio)
    (hvrlt : verticalRatio < 1)
    (S : Finset NativeGpreBoundaryContext) :
    2 *
        ((c2OddCoreLogCoefficient (8 * M) (p * q) : ℂ) *
          positiveDirichletValue s (p * q - 1)) -
      ((c2OddCoreLogCoefficient (4 * M) (p * q) : ℂ) *
        positiveDirichletValue s (p * q - 1)) =
      (((1 / 2 : ℝ) *
        c2OddCoreFourScaleDefectReal M p *
          c2OddCoreFourScaleDefectReal M q : ℝ) : ℂ) *
        c2LogJetPrefixEnrichedReadout
          verticalRatio hvrpos.le hvrlt S (p * q - 1)
          (c2LogJetPrefixEnrichedAnalysis
            verticalRatio S s (p * q - 1)) := by
  rw [
    c2OddCoreLogCoefficient_distinct_primes_richardson_mul_positiveDirichletValue
      hp hpodd hq hqodd hpq hpM hqM hpqM s,
    c2LogJetPrefixEnrichedReadout_analysis
      verticalRatio hvrpos hvrlt S s (p * q - 1)]

end

end CPFormal.Analytic.Cp
