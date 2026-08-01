import CPFormal.Analytic.CpNativeGpreFiniteTowerCollapse
import CPFormal.Analytic.CpGenuineGpreLogJetGreenBulkReadout

/-!
# TFVD log-jet commutator as an explicit native tower moment

The preceding finite collapse turns every weighted provenance coordinate into
a moment of a source constructed at the corresponding material tower level.
This module applies that adjoint operation to the reflected ordinary/log-jet
wedge.

For one active provenance context, the source is assembled from the four scalar
values (ordinary/log-jet at the parameter and its reflection) before the wedge
is read.  These are not four geometric legs.  The zero-based analytic edge `n`
is carried by the positive native Cp-block cell `p * (n + 1)`.  Its tower
moment is the real part of the scaled reflected wedge.  Specializing the second
channel to the phase-normalized Cp log-jet commutator gives the exact local
summand used by the enriched Green bulk readout.

A finite prefix source then sums these local vectors.  Its moment is exactly the
normalized commutator trace, hence exactly the finite prime Green bulk.  The
construction remains camera-by-camera at this checkpoint; it does not assert
that the sources for different primes are already one common tower vector.
Here `p : Nat.Primes` selects a prime observable of the arithmetic carrier; it
does not make the underlying carry geometry prime-exclusive.

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
  have hcoeffC :
      ((nativeGpreTowerCoordinateCoefficient
        (c.withRole .value) : ℝ) : ℂ) ≠ 0 := by
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
    calc
      (scale * (starRingEnd ℂ) (psi c.cell) *
            (((nativeGpreTowerCoordinateCoefficient
              (c.withRole .value) : ℝ) : ℂ))⁻¹) *
          (phiSharp c.cell *
            ((nativeGpreTowerCoordinateCoefficient
              (c.withRole .value) : ℝ) : ℂ)) =
        scale * (starRingEnd ℂ) (psi c.cell) * phiSharp c.cell *
          ((((nativeGpreTowerCoordinateCoefficient
            (c.withRole .value) : ℝ) : ℂ))⁻¹ *
            ((nativeGpreTowerCoordinateCoefficient
              (c.withRole .value) : ℝ) : ℂ)) := by ring
      _ = scale * (starRingEnd ℂ) (psi c.cell) * phiSharp c.cell := by
        simp [hcoeffC]
  have hsecond :
      (-(scale * (starRingEnd ℂ) (phi c.cell)) *
          (nativeGpreBoundaryValueCoefficientComplex c)⁻¹) *
        nativeGpreBoundaryValueLift psiSharp c =
      -(scale * (starRingEnd ℂ) (phi c.cell) * psiSharp c.cell) := by
    rw [nativeGpreBoundaryValueLift_apply]
    unfold nativeGpreBoundaryValueCoefficientComplex
    calc
      (-(scale * (starRingEnd ℂ) (phi c.cell)) *
            (((nativeGpreTowerCoordinateCoefficient
              (c.withRole .value) : ℝ) : ℂ))⁻¹) *
          (psiSharp c.cell *
            ((nativeGpreTowerCoordinateCoefficient
              (c.withRole .value) : ℝ) : ℂ)) =
        -(scale * (starRingEnd ℂ) (phi c.cell) * psiSharp c.cell) *
          ((((nativeGpreTowerCoordinateCoefficient
            (c.withRole .value) : ℝ) : ℂ))⁻¹ *
            ((nativeGpreTowerCoordinateCoefficient
              (c.withRole .value) : ℝ) : ℂ)) := by ring
      _ = -(scale * (starRingEnd ℂ) (phi c.cell) * psiSharp c.cell) := by
        simp [hcoeffC]
  rw [hfirst, hsecond]
  unfold reflectedLogJetEdgeWedge
  rw [mul_sub]
  simp only [Complex.sub_re, Complex.neg_re]
  ring

/-- Critical-amplitude/logarithm normalizer used by the finite enriched Green
readout. -/
def nativeGpreCpLogJetGreenNormalizer (p : Nat.Primes) : ℂ :=
  -(((primeCarryAmplitudeRatio p : ℝ) : ℂ) /
    ((Real.log (p : ℝ) : ℝ) : ℂ))

/-- Canonical active provenance context for analytic edge `n`.  The positive
native cell `p * (n + 1)` is the initial cell of the corresponding Cp block;
it is deliberately distinct from the zero-based analytic edge index.  The
material level `n + 1` keeps different analytic edges on different positive
tower coordinates. -/
def nativeGpreCanonicalActiveCommutatorContext
    (p : Nat.Primes) (tau n : ℕ) : NativeGpreBoundaryContext where
  arithmeticPrime := ⟨p⟩
  time := ⟨tau⟩
  cell := (p : ℕ) * (n + 1)
  corner := .lowerLeft
  orientation := .original
  leg := .left
  jordanDivisor := ⟨1⟩
  towerPrime := ⟨p⟩
  towerLevel := ⟨n + 1⟩

/-- The canonical Cp-block context is genuinely active.  In particular, this
removes the impossible demand for an active native coordinate at cell zero. -/
theorem nativeGpreCanonicalActiveCommutatorContext_active
    (p : Nat.Primes) (tau n : ℕ) :
    nativeGpreTowerCoordinateCoefficient
      ((nativeGpreCanonicalActiveCommutatorContext p tau n).withRole .value) ≠
        0 := by
  have hp0 : (p : ℕ) ≠ 0 := p.prop.ne_zero
  have hpn1 : (p : ℕ) ≠ 1 := p.prop.ne_one
  have hn1 : n + 1 ≠ 0 := by omega
  have hcell : (p : ℕ) * (n + 1) ≠ 0 := mul_ne_zero hp0 hn1
  simp [nativeGpreCanonicalActiveCommutatorContext,
    NativeGpreBoundaryContext.withRole,
    nativeGpreTowerCoordinateCoefficient,
    nativeGpreCornerDivisorCoordinate,
    nativeGpreDivisorCoordinate,
    nativeGpreJordanBracket,
    nativeGprePairValuation,
    nativeGpreCornerU, nativeGpreCornerV,
    nativeGpreCornerSign,
    nativeGpreOrientationFactor,
    nativeGpreGraphRoleFactor,
    nativeUnitMassTowerProfile,
    nativeGpreJordanArithmetic, nativeGprePowerArithmetic,
    nativeGpreHArithmetic, nativeGpreValuationPowerArithmetic,
    hp0, hpn1, hcell, p.prop.factorization_self]
  constructor
  · constructor
    · constructor
      · positivity
      · intro h
        have hncast : (0 : ℚ) < (n : ℚ) + 1 := by positivity
        linarith
    · have hpnonneg : (0 : ℝ) ≤ (p : ℝ) := by positivity
      linarith
  · have hncast : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    intro h
    linarith

/-- Explicit source of analytic commutator edge `n`, carried at an independently
specified positive native provenance cell. -/
noncomputable def nativeGpreCanonicalCpLogJetCommutatorEdgeTowerSource
    (p : Nat.Primes) (s : ℂ) (n : ℕ)
    (c : NativeGpreBoundaryContext) : NativeGpreTowerHilbert :=
  nativeGpreScaledReflectedWedgeTowerSource
    (nativeGpreCpLogJetGreenNormalizer p)
    (nativeGpreSingleComplexEdgeCore c.cell
      (positiveDirichletGradient s n))
    (nativeGpreSingleComplexEdgeCore c.cell
      (phaseNormalizedCpLogJetCommutator (p : ℕ) s n))
    (nativeGpreSingleComplexEdgeCore c.cell
      (positiveDirichletGradient (reflectedParameter s) n))
    (nativeGpreSingleComplexEdgeCore c.cell
      (phaseNormalizedCpLogJetCommutator
        (p : ℕ) (reflectedParameter s) n))
    c

/-- The local source reads the normalized commutator wedge itself. -/
theorem inner_nativeGpreTowerProfileVector_canonicalCpLogJetCommutatorEdgeTowerSource
    (p : Nat.Primes) (s : ℂ) (n : ℕ)
    (c : NativeGpreBoundaryContext)
    (hactive :
      nativeGpreTowerCoordinateCoefficient (c.withRole .value) ≠ 0) :
    inner ℝ
        (nativeGpreTowerProfileVector
          c.towerPrime.val c.time.val)
        (nativeGpreCanonicalCpLogJetCommutatorEdgeTowerSource p s n c) =
      (nativeGpreCpLogJetGreenNormalizer p *
        canonicalReflectedCpLogJetCommutatorWedge
          (p : ℕ) n s).re := by
  unfold nativeGpreCanonicalCpLogJetCommutatorEdgeTowerSource
    canonicalReflectedCpLogJetCommutatorWedge
  simpa using
    (inner_nativeGpreTowerProfileVector_scaledReflectedWedgeTowerSource
      (nativeGpreCpLogJetGreenNormalizer p)
      (nativeGpreSingleComplexEdgeCore c.cell
        (positiveDirichletGradient s n))
      (nativeGpreSingleComplexEdgeCore c.cell
        (phaseNormalizedCpLogJetCommutator (p : ℕ) s n))
      (nativeGpreSingleComplexEdgeCore c.cell
        (positiveDirichletGradient (reflectedParameter s) n))
      (nativeGpreSingleComplexEdgeCore c.cell
        (phaseNormalizedCpLogJetCommutator
          (p : ℕ) (reflectedParameter s) n))
      c hactive)

/-- Sum of the local sources before any scalar commutator trace is taken. -/
noncomputable def nativeGpreCanonicalCpLogJetCommutatorPrefixTowerSource
    (p : Nat.Primes) (tau N : ℕ) (s : ℂ) : NativeGpreTowerHilbert :=
  ∑ n ∈ Finset.range N,
    nativeGpreCanonicalCpLogJetCommutatorEdgeTowerSource
      p s n (nativeGpreCanonicalActiveCommutatorContext p tau n)

/-- Real normalized commutator trace in consecutive-edge form. -/
def finiteNativeGpreCanonicalCpLogJetCommutatorRealTrace
    (p : Nat.Primes) (N : ℕ) (s : ℂ) : ℝ :=
  ∑ n ∈ Finset.range N,
    (nativeGpreCpLogJetGreenNormalizer p *
      canonicalReflectedCpLogJetCommutatorWedge (p : ℕ) n s).re

/-- The prefix source has exactly the preceding finite normalized commutator
trace as its native tower moment. -/
theorem inner_nativeGpreTowerProfileVector_canonicalCpLogJetCommutatorPrefixTowerSource
    (p : Nat.Primes) (tau N : ℕ) (s : ℂ) :
    inner ℝ (nativeGpreTowerProfileVector (p : ℕ) tau)
        (nativeGpreCanonicalCpLogJetCommutatorPrefixTowerSource
          p tau N s) =
      finiteNativeGpreCanonicalCpLogJetCommutatorRealTrace p N s := by
  classical
  unfold nativeGpreCanonicalCpLogJetCommutatorPrefixTowerSource
    finiteNativeGpreCanonicalCpLogJetCommutatorRealTrace
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simpa [nativeGpreCanonicalActiveCommutatorContext] using
    (inner_nativeGpreTowerProfileVector_canonicalCpLogJetCommutatorEdgeTowerSource
      p s n (nativeGpreCanonicalActiveCommutatorContext p tau n)
      (nativeGpreCanonicalActiveCommutatorContext_active p tau n))

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
    (p : Nat.Primes) (tau M : ℕ) (s : ℂ) :
    inner ℝ (nativeGpreTowerProfileVector (p : ℕ) tau)
        (nativeGpreCanonicalCpLogJetCommutatorPrefixTowerSource
          p tau (3 * M) s) =
      finiteNativeGpreLogJetGreenBulkReadout p M s := by
  rw [inner_nativeGpreTowerProfileVector_canonicalCpLogJetCommutatorPrefixTowerSource,
    finiteNativeGpreCanonicalCpLogJetCommutatorRealTrace_three_mul_eq_greenBulk]

end

end CPFormal.Analytic.Cp
