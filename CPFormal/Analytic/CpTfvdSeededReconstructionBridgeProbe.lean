import CPFormal.Analytic.CpFiniteSeededTfvdGreenIdentity
import CPFormal.Analytic.CpNativeGpreTfvdAnalysis
import CPFormal.Analytic.CpC2LogJetGpreLift

/-!
# Seeded TFVD reconstruction checkpoint and exact radial gate

This module records the successful part of the diagnostic reconstruction route
without leaving a deliberately failing theorem in the build.

At a Genuine zero:

* the seeded TFVD Genuine readout tends to zero;
* the weighted TFVD analysis has an exact continuous left inverse;
* the ordinary Dirichlet-gradient prefix is reconstructed without loss;
* the log-jet prefix is reconstructed without loss;
* the moving endpoint tends to zero.

The final theorem then identifies the remaining seeded radial closure exactly:
it holds if and only if the real part of the parameter is `1 / 2`.  Thus the
reconstruction machinery is certified and the residual gate is kept explicit,
without an axiom, `sorry`, `admit`, or a renamed confinement hypothesis.
-/

open scoped BigOperators Topology lp ENNReal NNReal

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-- The first `N` ordinary Dirichlet-gradient edges as a finitely supported
native state.  This is the value-field companion of `c2LogJetPrefixCore`. -/
def c2DirichletGradientPrefixCore (s : ℂ) (N : ℕ) :
    NativeGpreComplexEdgeCore :=
  Finsupp.onFinset (Finset.range N)
    (fun n ↦ if n < N then positiveDirichletGradient s n else 0)
    (by
      intro n hn
      by_contra hmem
      have hnlt : ¬ n < N := by
        simpa only [Finset.mem_range, not_false_eq_true] using hmem
      simp [hnlt] at hn)

@[simp] theorem c2DirichletGradientPrefixCore_apply
    (s : ℂ) (N n : ℕ) :
    c2DirichletGradientPrefixCore s N n =
      if n < N then positiveDirichletGradient s n else 0 := by
  classical
  simp [c2DirichletGradientPrefixCore]

/-- Enriched TFVD analysis of the ordinary gradient prefix. -/
def c2DirichletGradientPrefixEnrichedAnalysis
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (s : ℂ) (N : ℕ) :
    NativeGpreFiniteTfvdAnalysisCarrier S :=
  nativeGpreFiniteTfvdAnalysis q S
    (nativeGpreCanonicalVerticalRealization
      (c2DirichletGradientPrefixCore s N))

/-- Exact TFVD reconstruction of the ordinary gradient prefix. -/
theorem c2DirichletGradientPrefixEnrichedAnalysis_reconstruction
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (s : ℂ) (N : ℕ) :
    nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S
        (c2DirichletGradientPrefixEnrichedAnalysis q S s N) =
      nativeGpreCanonicalVerticalRealization
        (c2DirichletGradientPrefixCore s N) := by
  exact nativeGpreFiniteTfvdReconstruction_analysis
    q hqpos hq1 S
      (nativeGpreCanonicalVerticalRealization
        (c2DirichletGradientPrefixCore s N))

/--
All pieces accepted by the diagnostic kernel run, now packaged as one green
checkpoint.  The provenance atlas `S` remains arbitrary; no empty-atlas
shortcut is used in the statement.
-/
theorem genuine_zero_tfvd_seeded_reconstruction_checkpoint
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
        (fun M : ℕ ↦
          finiteSeededEnrichedTfvdGenuineReadout M kappa omega
            (canonicalSeededEnrichedTfvdGenuinePort kappa omega s))
        atTop (nhds 0) ∧
      nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S ∘L
          nativeGpreFiniteTfvdAnalysis q S =
        ContinuousLinearMap.id ℂ CarryVerticalL2 ∧
      (∀ M : ℕ,
        nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S
            (c2DirichletGradientPrefixEnrichedAnalysis q S s (3 * M)) =
          nativeGpreCanonicalVerticalRealization
            (c2DirichletGradientPrefixCore s (3 * M))) ∧
      (∀ M : ℕ,
        nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S
            (c2LogJetPrefixEnrichedAnalysis q S s (3 * M)) =
          nativeGpreCanonicalVerticalRealization
            (c2LogJetPrefixCore s (3 * M))) ∧
      Tendsto
        (fun M : ℕ ↦ finiteCanonicalSeededTfvdGreenMovingEndpoint M s)
        atTop (nhds 0) := by
  refine ⟨
    finiteSeededEnrichedTfvdGenuineReadout_tendsto_zero_of_genuine_zero
      hs hzero hkappa omega homega,
    nativeGpreFiniteTfvdReconstruction_comp_analysis q hqpos hq1 S,
    ?_, ?_,
    finiteCanonicalSeededTfvdGreenMovingEndpoint_tendsto_zero_of_genuine_zero
      hs hzero⟩
  · intro M
    exact c2DirichletGradientPrefixEnrichedAnalysis_reconstruction
      q hqpos hq1 S s (3 * M)
  · intro M
    exact c2LogJetPrefixEnrichedAnalysis_reconstruction
      q hqpos hq1 S s (3 * M)

/--
Exact kernel-level status of the remaining radial gate.  Once all reconstructed
pieces and the vanishing moving endpoint are retained, seeded radial closure is
neither weaker nor stronger than the critical half-abscissa at a Genuine zero.
-/
theorem seededTfvdGreenRadialClosureAt_iff_re_eq_half_of_genuine_zero
    (p : ℕ) (hp : Nat.Prime p)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    SeededTfvdGreenRadialClosureAt p kappa omega s ↔
      s.re = (1 : ℝ) / 2 := by
  rw [seededTfvdGreenRadialClosureAt_iff_coupledGreenFlux_tendsto_zero_of_genuine_zero
    p hp hkappa omega homega hs hzero]
  constructor
  · intro hflux
    have hcritical :=
      criticalDisplacement_eq_zero_of_alignedGenuineGreenFlux_tendsto_zero
        p hp hs hzero hflux
    unfold criticalDisplacement at hcritical
    linarith
  · intro hre
    apply alignedGenuineGreenFlux_tendsto_zero_of_criticalDisplacement
      p hp hs hzero
    unfold criticalDisplacement
    linarith

end

end CPFormal.Analytic.Cp
