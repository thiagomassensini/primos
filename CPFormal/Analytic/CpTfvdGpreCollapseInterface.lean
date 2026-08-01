import CPFormal.Analytic.CpTfvdSeededNativeMomentContraction

/-!
# Interface for the missing TFVD--G_pre collapse

This file does not assume uniform Bessel boundedness and does not manufacture
a tower source from the target coordinates.  It isolates the only new datum
still required after the seeded TFVD reconstruction and the native contraction:
a fixed, atlas-independent collapse of the two same-edge TFVD states whose
native tower moments are the enriched Green readouts.
-/

open scoped BigOperators Topology lp ENNReal NNReal

namespace CPFormal.Analytic.Cp

noncomputable section

/-- A candidate collapse takes the ordinary and log-jet same-edge states to
one real native tower state.  No linearity is imposed because the Green wedge
is bilinear in the two inputs. -/
abbrev NativeGpreTfvdCollapse :=
  NativeGpreTfvdProductState →
    NativeGpreTfvdProductState → NativeGpreTowerHilbert

/-- The source obtained by applying a candidate collapse to the two canonical
same-edge prefixes used by the seeded TFVD checkpoint. -/
def seededTfvdGpreCollapsedSource
    (collapse : NativeGpreTfvdCollapse)
    (M : ℕ) (s : ℂ) : NativeGpreTowerHilbert :=
  collapse
    (nativeGpreTfvdSameEdgeGlue nativeGpreCanonicalVerticalRealization
      (c2DirichletGradientPrefixCore s (3 * M)))
    (nativeGpreTfvdSameEdgeGlue nativeGpreCanonicalVerticalRealization
      (c2LogJetPrefixCore s (3 * M)))

/-- Reconstruction really returns the vertical leg of the same-edge glue.
This is the exact part already supplied by TFVD; it does not yet construct a
real tower state. -/
theorem nativeGpreTfvdReconstruction_analysis_eq_sameEdgeGlue_fst
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (x : NativeGpreComplexEdgeCore) :
    nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S
        (nativeGpreFiniteTfvdAnalysis q S
          (nativeGpreCanonicalVerticalRealization x)) =
      (nativeGpreTfvdSameEdgeGlue
        nativeGpreCanonicalVerticalRealization x).1 := by
  rw [nativeGpreFiniteTfvdReconstruction_analysis q hqpos hq1 S]
  rfl

/-- The missing coordinate identity, stated without a boundedness conclusion.
It asks the explicit collapsed source to reproduce every prime readout. -/
def IsSeededTfvdGpreMomentCollapseAt
    (collapse : NativeGpreTfvdCollapse)
    (M : ℕ) (s : ℂ) : Prop :=
  ∀ p : Nat.Primes,
    inner ℝ (nativeGpreTowerProfileVector (p : ℕ) 1)
        (seededTfvdGpreCollapsedSource collapse M s) =
      finiteEnrichedNativeGpreLogJetGreenBulkReadout
        p M 1 (fun _ => 1) s

/-- The coordinate identity is exactly the native moment realization needed
by the already-green contraction theorem. -/
theorem isNativeGprePrimeMomentRealizationAt_of_tfvdGpreMomentCollapse
    (collapse : NativeGpreTfvdCollapse)
    (M : ℕ) (s : ℂ)
    (hcollapse : IsSeededTfvdGpreMomentCollapseAt collapse M s) :
    IsNativeGprePrimeMomentRealizationAt 1 (3 * M) s
      (seededTfvdGpreCollapsedSource collapse M s) := by
  intro p
  rw [hcollapse p,
    finiteEnrichedNativeGpreLogJetGreenBulkReadout_eq
      p M (by norm_num) (fun _ => 1) (by intro m; norm_num) s]

/-- Once the missing coordinate identity is available at one nonempty cutoff,
the existing contraction and TFVD--Bessel theorem force the half-abscissa. -/
theorem re_eq_half_of_tfvdGpreMomentCollapse
    (collapse : NativeGpreTfvdCollapse)
    (M : ℕ) (hM : 0 < M) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (hcollapse : IsSeededTfvdGpreMomentCollapseAt collapse M s) :
    s.re = (1 : ℝ) / 2 := by
  exact re_eq_half_of_seededTfvd_nativeMomentRealization
    M hM hs (seededTfvdGpreCollapsedSource collapse M s)
      (isNativeGprePrimeMomentRealizationAt_of_tfvdGpreMomentCollapse
        collapse M s hcollapse)

/-- Global zero-side formulation of the sole remaining construction. -/
def GenuineZerosAdmitSeededTfvdGpreMomentCollapse
    (collapse : NativeGpreTfvdCollapse) : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip → genuineContinuation s = 0 →
    IsSeededTfvdGpreMomentCollapseAt collapse 1 s

/-- Planned terminal theorem, conditional only on the explicit collapse law.
All work after that law is discharged by existing green results. -/
theorem genuine_zero_re_eq_half_of_tfvdGpreCollapse
    (collapse : NativeGpreTfvdCollapse)
    (hcollapse : GenuineZerosAdmitSeededTfvdGpreMomentCollapse collapse)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    s.re = (1 : ℝ) / 2 := by
  exact re_eq_half_of_tfvdGpreMomentCollapse
    collapse 1 (by norm_num) hs (hcollapse hs hzero)

end


end CPFormal.Analytic.Cp
