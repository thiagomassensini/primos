import CPFormal.Analytic.CpFiniteSeededTfvdGreenIdentity
import CPFormal.Analytic.CpNativeGpreTfvdAnalysis
import CPFormal.Analytic.CpC2LogJetGpreLift

/-!
# Diagnostic probe: seeded TFVD reconstruction versus the radial Green closure

This probe tests the native route suggested by the exact identities already in
`main`:

* the seeded Genuine TFVD readout tends to zero at a Genuine zero;
* the weighted TFVD analysis has an exact continuous left inverse;
* both the ordinary Dirichlet-gradient prefix and its log-jet prefix are
  reconstructed without loss;
* the moving endpoint tends to zero;
* the seeded TFVD--Green identity separates the remaining radial observable
  from the provenance defect.

The intended conclusion is `SeededTfvdGreenRadialClosureAt`, hence vanishing of
the coupled Green flux and finally mass compatibility.  No axiom, `sorry` or
`admit` is used.  The deliberate diagnostic stop prints the exact goal that
remains after all available reconstruction facts have been placed in context.
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
Direct test of the proposed final composition.

After the exact identities are introduced, Lean is asked for the coupled Green
flux limit.  A successful automatic composition would close the theorem.  On
failure, `trace_state` records the remaining bridge without renaming it as an
assumption.
-/
theorem genuine_zero_tfvd_seeded_reconstruction_bridge_probe
    (p : ℕ) (hp : Nat.Prime p)
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    SeededTfvdGreenRadialClosureAt p kappa omega s := by
  have hseededReadout :=
    finiteSeededEnrichedTfvdGenuineReadout_tendsto_zero_of_genuine_zero
      hs hzero hkappa omega homega

  have htfvdOperatorIdentity :=
    nativeGpreFiniteTfvdReconstruction_comp_analysis
      q hqpos hq1 S

  have hvalueReconstruction : ∀ M : ℕ,
      nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S
          (c2DirichletGradientPrefixEnrichedAnalysis q S s (3 * M)) =
        nativeGpreCanonicalVerticalRealization
          (c2DirichletGradientPrefixCore s (3 * M)) := by
    intro M
    exact c2DirichletGradientPrefixEnrichedAnalysis_reconstruction
      q hqpos hq1 S s (3 * M)

  have hlogJetReconstruction : ∀ M : ℕ,
      nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S
          (c2LogJetPrefixEnrichedAnalysis q S s (3 * M)) =
        nativeGpreCanonicalVerticalRealization
          (c2LogJetPrefixCore s (3 * M)) := by
    intro M
    exact c2LogJetPrefixEnrichedAnalysis_reconstruction
      q hqpos hq1 S s (3 * M)

  have hendpoint :=
    finiteCanonicalSeededTfvdGreenMovingEndpoint_tendsto_zero_of_genuine_zero
      hs hzero

  apply
    (seededTfvdGreenRadialClosureAt_iff_coupledGreenFlux_tendsto_zero_of_genuine_zero
      p hp hkappa omega homega hs hzero).2

  trace_state
  fail "diagnostic stop after exposing the TFVD reconstruction-to-radial bridge"

end

end CPFormal.Analytic.Cp
