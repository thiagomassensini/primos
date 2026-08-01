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

The finite ledger is then simplified before taking any limit: the moving
endpoint cancels the aligned bracket boundary exactly, so the seeded radial
observable is the pure radial coefficient times the positive reflected pairing.
Consequently its closure is equivalent to the critical half-abscissa throughout
the Genuine strip, independently of a zero hypothesis.

No axiom, `sorry`, `admit`, or renamed confinement hypothesis is used.
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
Exact finite cancellation of the return endpoint against the aligned bracket
boundary.  The seeded TFVD observable is therefore the pure radial Green bulk,
with no zero or limiting hypothesis.
-/
theorem
    finiteCanonicalSeededTfvdGreenRadialClosureObservable_eq_radialDifference_mul_pairing
    (p : ℕ) (hp : Nat.Prime p)
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    (s : ℂ) :
    finiteCanonicalSeededTfvdGreenRadialClosureObservable
        p M kappa omega s =
      cpRadialDifference p (criticalDisplacement s.re) *
        (finiteReflectedGradientPairing (3 * M) s).re := by
  rw [
    finiteCanonicalSeededTfvdGreenRadialClosureObservable_eq_flux_add_endpoint
      p hp M hkappa omega homega s,
    finiteCanonicalAngularBracketCoupledGenuineGreenFlux_eq_radialDifference_mul_pairing
      p M hp s,
    finiteCanonicalSeededTfvdGreenMovingEndpoint_eq_neg_boundary]
  unfold finiteCanonicalAngularBracketCoupledSignedBoundary
  simp only [Complex.neg_re]
  ring

/--
The radial closure gate itself is exactly the vanishing of the transverse carry
coefficient.  Positivity and monotonicity of the reflected pairing prevent a
nonzero constant radial coefficient from converging to zero.
-/
theorem seededTfvdGreenRadialClosureAt_iff_criticalDisplacement_eq_zero
    (p : ℕ) (hp : Nat.Prime p)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    SeededTfvdGreenRadialClosureAt p kappa omega s ↔
      criticalDisplacement s.re = 0 := by
  constructor
  · intro hclosure
    unfold SeededTfvdGreenRadialClosureAt at hclosure
    let c : ℝ := cpRadialDifference p (criticalDisplacement s.re)
    let pairingRe : ℕ → ℝ :=
      fun M ↦ (finiteReflectedGradientPairing (3 * M) s).re
    have hfun :
        (fun M : ℕ ↦
          finiteCanonicalSeededTfvdGreenRadialClosureObservable
            p M kappa omega s) =
          (fun M : ℕ ↦ c * pairingRe M) := by
      funext M
      dsimp [c, pairingRe]
      exact
        finiteCanonicalSeededTfvdGreenRadialClosureObservable_eq_radialDifference_mul_pairing
          p hp M hkappa omega homega s
    rw [hfun] at hclosure
    have hpositive : 0 < pairingRe 1 := by
      dsimp [pairingRe]
      exact finiteReflectedGradientPairing_re_pos (by norm_num) hs
    have hmonotone := finiteReflectedGradientPairing_re_monotone hs
    have hbound : ∀ᶠ M in atTop, pairingRe 1 ≤ pairingRe M :=
      eventually_atTop.2 ⟨1, fun M hM ↦ hmonotone (by omega)⟩
    have hc : c = 0 :=
      constant_eq_zero_of_tendsto_mul_of_eventually_pos_lower_bound
        hpositive hbound hclosure
    dsimp [c] at hc
    exact
      (cpRadialDifference_eq_zero_iff
        p hp (criticalDisplacement s.re)).1 hc
  · intro hcritical
    unfold SeededTfvdGreenRadialClosureAt
    have hradial :
        cpRadialDifference p (criticalDisplacement s.re) = 0 :=
      (cpRadialDifference_eq_zero_iff
        p hp (criticalDisplacement s.re)).2 hcritical
    have hfun :
        (fun M : ℕ ↦
          finiteCanonicalSeededTfvdGreenRadialClosureObservable
            p M kappa omega s) =
          (fun _ : ℕ ↦ (0 : ℝ)) := by
      funext M
      rw [
        finiteCanonicalSeededTfvdGreenRadialClosureObservable_eq_radialDifference_mul_pairing
          p hp M hkappa omega homega s,
        hradial,
        zero_mul]
    rw [hfun]
    exact tendsto_const_nhds

/-- The same exact gate in the original radial coordinate. -/
theorem seededTfvdGreenRadialClosureAt_iff_re_eq_half
    (p : ℕ) (hp : Nat.Prime p)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    SeededTfvdGreenRadialClosureAt p kappa omega s ↔
      s.re = (1 : ℝ) / 2 := by
  rw [seededTfvdGreenRadialClosureAt_iff_criticalDisplacement_eq_zero
    p hp hkappa omega homega hs]
  unfold criticalDisplacement
  constructor <;> intro h <;> linarith

/-- Corollary retaining the Genuine-zero context used by the diagnostic route. -/
theorem seededTfvdGreenRadialClosureAt_iff_re_eq_half_of_genuine_zero
    (p : ℕ) (hp : Nat.Prime p)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (_hzero : genuineContinuation s = 0) :
    SeededTfvdGreenRadialClosureAt p kappa omega s ↔
      s.re = (1 : ℝ) / 2 :=
  seededTfvdGreenRadialClosureAt_iff_re_eq_half
    p hp hkappa omega homega hs

end

end CPFormal.Analytic.Cp
