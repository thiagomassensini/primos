import CPFormal.Analytic.CpNativeGpreFiniteTowerCollapse
import CPFormal.Analytic.CpGenuineGpreLogJetGreenBulkReadout

/-!
# TFVD log-jet commutator as an explicit native tower moment

The preceding finite collapse turns every weighted provenance coordinate into
a moment of a source constructed at the corresponding material tower level.
This module applies that adjoint operation to the reflected ordinary/log-jet
wedge.

For one active provenance context, the source is assembled from the four edge
values before the scalar wedge is read.  Its tower moment is the real part of
the scaled reflected wedge.  Specializing the second leg to the phase-normalized
Cp log-jet commutator gives the exact local summand used by the enriched Green
bulk readout.

A finite prefix atlas then sums these local sources.  Its moment is exactly the
normalized commutator trace, hence exactly the finite prime Green bulk.  The
construction remains camera-by-camera at this checkpoint; it does not assert
that the sources for different primes are already one common tower vector.

No target moment is used to define a source, and no zero, critical displacement,
`sorry`, `axiom` or `admit` appears.
-/

open scoped BigOperators ENNReal InnerProduct lp

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Complex value of the native value-role provenance coefficient. -/
def nativeGpreBoundaryValueCoefficientComplex
    (c : NativeGpreBoundaryContext) : ℂ :=
  (nativeGpreTowerCoordinateCoefficient (c.withRole .value) : ℂ)

/-- A one-edge core used only to place an independently defined edge value in
the same native carrier consumed by TFVD and G_pre. -/
def nativeGpreSingleComplexEdgeCore
    (n : ℕ) (z : ℂ) : NativeGpreComplexEdgeCore :=
  Finsupp.single n z

@[simp] theorem nativeGpreSingleComplexEdgeCore_apply_self
    (n : ℕ) (z : ℂ) :
    nativeGpreSingleComplexEdgeCore n z n = z := by
  simp [nativeGpreSingleComplexEdgeCore]

/-- Source whose moment is a scaled reflected wedge.  The inverse provenance
coefficient merely undoes the already-present coordinate encoding; the source
is still defined from the four edge values and their typed context, not from
the wedge scalar. -/
noncomputable def nativeGpreScaledReflectedWedgeTowerSource
    (scale : ℂ)
    (phi psi phiSharp psiSharp : NativeGpreComplexEdgeCore)
    (c : NativeGpreBoundaryContext) : NativeGpreTowerHilbert :=
  let a := nativeGpreBoundaryValueCoefficientComplex c
  nativeGpreWeightedBoundaryContextTowerSource
      (scale * (starRingEnd ℂ) (psi c.cell) * a⁻¹) phiSharp c +
    nativeGpreWeightedBoundaryContextTowerSource
      (-(scale * (starRingEnd ℂ) (phi c.cell)) * a⁻¹) psiSharp c

/-- Exact one-context wedge moment. -/
theorem inner_nativeGpreTowerProfileVector_scaledReflectedWedgeTowerSource
    (scale : ℂ)
    (phi psi phiSharp psiSharp : NativeGpreComplexEdgeCore)
    (c : NativeGpreBoundaryContext)
    (hactive :
      nativeGpreTowerCoordinateCoefficient (c.withRole .value) ≠ 0) :
    inner ℝ
        (nativeGpreTowerProfileVector
          c.towerPrime.val c.time.val)
        (nativeGpreScaledReflectedWedgeTowerSource
          scale phi psi phiSharp psiSharp c) =
      (scale * reflectedLogJetEdgeWedge
        (phi c.cell) (psi c.cell)
        (phiSharp c.cell) (psiSharp c.cell)).re := by
  have hactiveComplex : nativeGpreBoundaryValueCoefficientComplex c ≠ 0 := by
    unfold nativeGpreBoundaryValueCoefficientComplex
    exact_mod_cast hactive
  rw [nativeGpreScaledReflectedWedgeTowerSource, inner_add_right,
    inner_nativeGpreTowerProfileVector_weightedBoundaryContextTowerSource,
    inner_nativeGpreTowerProfileVector_weightedBoundaryContextTowerSource]
  have hfirst :
      (scale * (starRingEnd ℂ) (psi c.cell) *
          (nativeGpreBoundaryValueCoefficientComplex c)⁻¹) *
        nativeGpreBoundaryValueLift phiSharp c =
      scale * (starRingEnd ℂ) (psi c.cell) * phiSharp c.cell := by
    rw [nativeGpreBoundaryValueLift_apply]
    unfold nativeGpreBoundaryValueCoefficientComplex
    field_simp [hactiveComplex]
    ring
  have hsecond :
      (-(scale * (starRingEnd ℂ) (phi c.cell)) *
          (nativeGpreBoundaryValueCoefficientComplex c)⁻¹) *
        nativeGpreBoundaryValueLift psiSharp c =
      -(scale * (starRingEnd ℂ) (phi c.cell) * psiSharp c.cell) := by
    rw [nativeGpreBoundaryValueLift_apply]
    unfold nativeGpreBoundaryValueCoefficientComplex
    field_simp [hactiveComplex]
    ring
  rw [hfirst, hsecond]
  unfold reflectedLogJetEdgeWedge
  rw [mul_sub]
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re]
  ring

/-- Critical-amplitude/logarithm normalizer used by the finite enriched Green
readout. -/
def nativeGpreCpLogJetGreenNormalizer (p : Nat.Primes) : ℂ :=
  -(((primeCarryAmplitudeRatio p : ℝ) : ℂ) /
    ((Real.log (p : ℝ) : ℝ) : ℂ))

/-- Explicit source of one normalized Cp commutator edge. -/
noncomputable def nativeGpreCanonicalCpLogJetCommutatorEdgeTowerSource
    (p : Nat.Primes) (s : ℂ)
    (c : NativeGpreBoundaryContext) : NativeGpreTowerHilbert :=
  nativeGpreScaledReflectedWedgeTowerSource
    (nativeGpreCpLogJetGreenNormalizer p)
    (nativeGpreSingleComplexEdgeCore c.cell
      (positiveDirichletGradient s c.cell))
    (nativeGpreSingleComplexEdgeCore c.cell
      (phaseNormalizedCpLogJetCommutator (p : ℕ) s c.cell))
    (nativeGpreSingleComplexEdgeCore c.cell
      (positiveDirichletGradient (reflectedParameter s) c.cell))
    (nativeGpreSingleComplexEdgeCore c.cell
      (phaseNormalizedCpLogJetCommutator
        (p : ℕ) (reflectedParameter s) c.cell))
    c

/-- The local source reads the normalized commutator wedge itself. -/
theorem inner_nativeGpreTowerProfileVector_canonicalCpLogJetCommutatorEdgeTowerSource
    (p : Nat.Primes) (s : ℂ)
    (c : NativeGpreBoundaryContext)
    (hactive :
      nativeGpreTowerCoordinateCoefficient (c.withRole .value) ≠ 0) :
    inner ℝ
        (nativeGpreTowerProfileVector
          c.towerPrime.val c.time.val)
        (nativeGpreCanonicalCpLogJetCommutatorEdgeTowerSource p s c) =
      (nativeGpreCpLogJetGreenNormalizer p *
        canonicalReflectedCpLogJetCommutatorWedge
          (p : ℕ) c.cell s).re := by
  unfold nativeGpreCanonicalCpLogJetCommutatorEdgeTowerSource
    canonicalReflectedCpLogJetCommutatorWedge
  simpa using
    (inner_nativeGpreTowerProfileVector_scaledReflectedWedgeTowerSource
      (nativeGpreCpLogJetGreenNormalizer p)
      (nativeGpreSingleComplexEdgeCore c.cell
        (positiveDirichletGradient s c.cell))
      (nativeGpreSingleComplexEdgeCore c.cell
        (phaseNormalizedCpLogJetCommutator (p : ℕ) s c.cell))
      (nativeGpreSingleComplexEdgeCore c.cell
        (positiveDirichletGradient (reflectedParameter s) c.cell))
      (nativeGpreSingleComplexEdgeCore c.cell
        (phaseNormalizedCpLogJetCommutator
          (p : ℕ) (reflectedParameter s) c.cell))
      c hactive)

/-- A finite family of active native contexts, one for every edge in a prefix,
all living over the same material prime and arithmetic time. -/
structure NativeGpreActiveCommutatorPrefixContexts
    (p : Nat.Primes) (tau N : ℕ) where
  context : ℕ → NativeGpreBoundaryContext
  cell_eq : ∀ n, n < N → (context n).cell = n
  towerPrime_eq : ∀ n, n < N → (context n).towerPrime.val = (p : ℕ)
  time_eq : ∀ n, n < N → (context n).time.val = tau
  active : ∀ n, n < N →
    nativeGpreTowerCoordinateCoefficient
      ((context n).withRole .value) ≠ 0

/-- Sum of the local sources before any scalar commutator trace is taken. -/
noncomputable def nativeGpreCanonicalCpLogJetCommutatorPrefixTowerSource
    (p : Nat.Primes) (tau N : ℕ)
    (atlas : NativeGpreActiveCommutatorPrefixContexts p tau N)
    (s : ℂ) : NativeGpreTowerHilbert :=
  ∑ n ∈ Finset.range N,
    nativeGpreCanonicalCpLogJetCommutatorEdgeTowerSource
      p s (atlas.context n)

/-- Real normalized commutator trace in consecutive-edge form. -/
def finiteNativeGpreCanonicalCpLogJetCommutatorRealTrace
    (p : Nat.Primes) (N : ℕ) (s : ℂ) : ℝ :=
  ∑ n ∈ Finset.range N,
    (nativeGpreCpLogJetGreenNormalizer p *
      canonicalReflectedCpLogJetCommutatorWedge (p : ℕ) n s).re

/-- The prefix source has exactly the preceding finite normalized commutator
trace as its native tower moment. -/
theorem inner_nativeGpreTowerProfileVector_canonicalCpLogJetCommutatorPrefixTowerSource
    (p : Nat.Primes) (tau N : ℕ)
    (atlas : NativeGpreActiveCommutatorPrefixContexts p tau N)
    (s : ℂ) :
    inner ℝ (nativeGpreTowerProfileVector (p : ℕ) tau)
        (nativeGpreCanonicalCpLogJetCommutatorPrefixTowerSource
          p tau N atlas s) =
      finiteNativeGpreCanonicalCpLogJetCommutatorRealTrace p N s := by
  classical
  unfold nativeGpreCanonicalCpLogJetCommutatorPrefixTowerSource
    finiteNativeGpreCanonicalCpLogJetCommutatorRealTrace
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnlt : n < N := Finset.mem_range.mp hn
  have hcell := atlas.cell_eq n hnlt
  have hp := atlas.towerPrime_eq n hnlt
  have htau := atlas.time_eq n hnlt
  simpa [hcell, hp, htau] using
    (inner_nativeGpreTowerProfileVector_canonicalCpLogJetCommutatorEdgeTowerSource
      p s (atlas.context n) (atlas.active n hnlt))

/-- Real part commutes with a finite consecutive sum. -/
theorem complex_re_sum_range
    (f : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N, f n).re =
      ∑ n ∈ Finset.range N, (f n).re := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        Complex.add_re, ih]

/-- The consecutive normalized commutator trace is exactly the existing
finite enriched Green bulk readout. -/
theorem finiteNativeGpreCanonicalCpLogJetCommutatorRealTrace_three_mul_eq_greenBulk
    (p : Nat.Primes) (M : ℕ) (s : ℂ) :
    finiteNativeGpreCanonicalCpLogJetCommutatorRealTrace p (3 * M) s =
      finiteNativeGpreLogJetGreenBulkReadout p M s := by
  unfold finiteNativeGpreCanonicalCpLogJetCommutatorRealTrace
    finiteNativeGpreLogJetGreenBulkReadout
  rw [finiteCanonicalCpLogJetCommutatorWedgeTrace_eq_range,
    Finset.mul_sum]
  exact
    (complex_re_sum_range
      (fun n => nativeGpreCpLogJetGreenNormalizer p *
        canonicalReflectedCpLogJetCommutatorWedge (p : ℕ) n s)
      (3 * M)).symm

/-- Final finite camera-by-camera checkpoint: the Green bulk is a literal
moment of the source extracted from its typed TFVD/G_pre edge provenance. -/
theorem inner_nativeGpreTowerProfileVector_canonicalCpLogJetCommutatorPrefixTowerSource_eq_greenBulk
    (p : Nat.Primes) (tau M : ℕ)
    (atlas : NativeGpreActiveCommutatorPrefixContexts p tau (3 * M))
    (s : ℂ) :
    inner ℝ (nativeGpreTowerProfileVector (p : ℕ) tau)
        (nativeGpreCanonicalCpLogJetCommutatorPrefixTowerSource
          p tau (3 * M) atlas s) =
      finiteNativeGpreLogJetGreenBulkReadout p M s := by
  rw [inner_nativeGpreTowerProfileVector_canonicalCpLogJetCommutatorPrefixTowerSource,
    finiteNativeGpreCanonicalCpLogJetCommutatorRealTrace_three_mul_eq_greenBulk]

end

end CPFormal.Analytic.Cp
