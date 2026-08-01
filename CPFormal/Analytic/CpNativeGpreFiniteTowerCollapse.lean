import CPFormal.Analytic.CpNativeGprePrimeCarryContraction
import CPFormal.Analytic.CpNativeGpreTfvdAnalysis

/-!
# Finite material-tower collapse of native G_pre provenance

The native provenance coefficient already contains one distinguished material
base factor

`nativeUnitMassTowerProfile p tau j = p^(-j*tau) / j`.

This module opens that factor before any camera synthesis.  A single
provenance context therefore determines a literal vector in the common tower
Hilbert space: all non-tower arithmetic data form its coefficient and the
material level chooses its coordinate.

The historical types `GpreArithmeticPrime` and `GpreTowerPrime` are wrappers
around `ℕ`; they contain no primality proof.  Accordingly, every identity in
this file is algebraic for arbitrary natural labels and in particular applies
to every integer material base `b > 1`.  This does not by itself assert that
every such label has a nonzero arithmetic coordinate.  Prime observables are a
later specialization, not the origin of this collapse.

Taking the moment of that source vector against the native profile of the same
camera and arithmetic time recovers exactly the real part of the original
provenance value coordinate.  The weighted version recovers every finite real
linear functional of those coordinates.  Summing over an arbitrary finite
fiber therefore gives a finite tower source whose moment is the corresponding
complete provenance readout.

No Green target, Genuine zero, critical displacement, `sorry`, `axiom` or
`admit` is used.  The construction is the algebraic source extraction needed
before the remaining same-edge TFVD/Green identification.
-/

open scoped BigOperators ENNReal InnerProduct lp

namespace CPFormal.Analytic.Cp

noncomputable section

/-- The native G_pre coordinate with the material tower profile removed.
All arithmetic, corner, orientation, leg and graph-role data remain literal. -/
noncomputable def nativeGpreTowerCoordinateKernel
    (c : NativeGpreContext) : ℝ :=
  if c.cell = 0 then 0
  else if c.towerPrime.val = c.arithmeticPrime.val then
    let u := nativeGpreCornerU c.cell c.corner
    let v := nativeGpreCornerV c.cell c.corner
    if c.jordanDivisor.val ∣ Nat.gcd u v then
      (nativeGpreCornerDivisorCoordinate
          c.cell c.corner c.arithmeticPrime.val c.time.val
          c.jordanDivisor.val : ℝ) *
        Real.log c.arithmeticPrime.val *
        nativeGpreOrientationFactor c.cell c.corner c.orientation *
        nativeGpreGraphRoleFactor c.towerLevel.val c.role
    else 0
  else 0

/-- Exact separation of the material profile from every typed provenance
coordinate. -/
theorem nativeGpreTowerCoordinateCoefficient_eq_kernel_mul_profile
    (c : NativeGpreContext) :
    nativeGpreTowerCoordinateCoefficient c =
      nativeGpreTowerCoordinateKernel c *
        nativeUnitMassTowerProfile
          c.towerPrime.val c.time.val c.towerLevel.val := by
  by_cases hcell : c.cell = 0
  · simp [nativeGpreTowerCoordinateCoefficient,
      nativeGpreTowerCoordinateKernel, hcell]
  · by_cases htower : c.towerPrime.val = c.arithmeticPrime.val
    · let u := nativeGpreCornerU c.cell c.corner
      let v := nativeGpreCornerV c.cell c.corner
      by_cases hd : c.jordanDivisor.val ∣ Nat.gcd u v
      · simp [nativeGpreTowerCoordinateCoefficient,
          nativeGpreTowerCoordinateKernel, hcell, htower, hd, u, v]
        ring
      · simp [nativeGpreTowerCoordinateCoefficient,
          nativeGpreTowerCoordinateKernel, hcell, htower, hd, u, v]
    · simp [nativeGpreTowerCoordinateCoefficient,
        nativeGpreTowerCoordinateKernel, hcell, htower]

/-- One typed provenance coordinate collapsed to its material tower level.
The source is constructed from the provenance data themselves, not from a
prescribed camera moment. -/
noncomputable def nativeGpreBoundaryContextTowerSource
    (x : NativeGpreComplexEdgeCore)
    (c : NativeGpreBoundaryContext) : NativeGpreTowerHilbert :=
  lp.single 2 c.towerLevel.val
    ((x c.cell).re *
      nativeGpreTowerCoordinateKernel (c.withRole .value))

/-- A native material profile reads back exactly the real provenance value of
one context. -/
theorem inner_nativeGpreTowerProfileVector_boundaryContextTowerSource
    (x : NativeGpreComplexEdgeCore)
    (c : NativeGpreBoundaryContext) :
    inner ℝ
        (nativeGpreTowerProfileVector
          c.towerPrime.val c.time.val)
        (nativeGpreBoundaryContextTowerSource x c) =
      (nativeGpreBoundaryValueLift x c).re := by
  calc
    inner ℝ
        (nativeGpreTowerProfileVector
          c.towerPrime.val c.time.val)
        (nativeGpreBoundaryContextTowerSource x c) =
      nativeUnitMassTowerProfile
          c.towerPrime.val c.time.val c.towerLevel.val *
        ((x c.cell).re *
          nativeGpreTowerCoordinateKernel (c.withRole .value)) := by
      unfold nativeGpreBoundaryContextTowerSource
      rw [lp.inner_single_right]
      simp [nativeGpreTowerProfileVector_apply, RCLike.inner_apply]
      ring
    _ = (x c.cell).re *
        nativeGpreTowerCoordinateCoefficient (c.withRole .value) := by
      rw [nativeGpreTowerCoordinateCoefficient_eq_kernel_mul_profile]
      simp [NativeGpreBoundaryContext.withRole]
      ring
    _ = (nativeGpreBoundaryValueLift x c).re := by
      rw [nativeGpreBoundaryValueLift_apply]
      simp

/-- Weighted extraction of one provenance coordinate.  This is the finite
Riesz-adjoint operation needed by the ordinary/log-jet wedges: the weight is
chosen before the moment is evaluated. -/
noncomputable def nativeGpreWeightedBoundaryContextTowerSource
    (weight : ℂ)
    (x : NativeGpreComplexEdgeCore)
    (c : NativeGpreBoundaryContext) : NativeGpreTowerHilbert :=
  lp.single 2 c.towerLevel.val
    ((weight * x c.cell).re *
      nativeGpreTowerCoordinateKernel (c.withRole .value))

/-- The weighted source reads back the real part of the weighted provenance
coordinate, without defining the source from that scalar target. -/
theorem inner_nativeGpreTowerProfileVector_weightedBoundaryContextTowerSource
    (weight : ℂ)
    (x : NativeGpreComplexEdgeCore)
    (c : NativeGpreBoundaryContext) :
    inner ℝ
        (nativeGpreTowerProfileVector
          c.towerPrime.val c.time.val)
        (nativeGpreWeightedBoundaryContextTowerSource weight x c) =
      (weight * nativeGpreBoundaryValueLift x c).re := by
  calc
    inner ℝ
        (nativeGpreTowerProfileVector
          c.towerPrime.val c.time.val)
        (nativeGpreWeightedBoundaryContextTowerSource weight x c) =
      nativeUnitMassTowerProfile
          c.towerPrime.val c.time.val c.towerLevel.val *
        ((weight * x c.cell).re *
          nativeGpreTowerCoordinateKernel (c.withRole .value)) := by
      unfold nativeGpreWeightedBoundaryContextTowerSource
      rw [lp.inner_single_right]
      simp [nativeGpreTowerProfileVector_apply, RCLike.inner_apply]
      ring
    _ = (weight * x c.cell).re *
        nativeGpreTowerCoordinateCoefficient (c.withRole .value) := by
      rw [nativeGpreTowerCoordinateCoefficient_eq_kernel_mul_profile]
      simp [NativeGpreBoundaryContext.withRole]
      ring
    _ = (weight * nativeGpreBoundaryValueLift x c).re := by
      rw [nativeGpreBoundaryValueLift_apply, ← mul_assoc]
      simp [Complex.mul_re]

/-- Finite source obtained by collapsing precisely the contexts of one
material base and one arithmetic time.  No primality hypothesis is present. -/
noncomputable def nativeGpreFiniteBoundaryTowerSourceAt
    (b tau : ℕ)
    (S : Finset NativeGpreBoundaryContext)
    (x : NativeGpreComplexEdgeCore) : NativeGpreTowerHilbert :=
  ∑ c ∈ S.filter
      (fun c => c.towerPrime.val = b ∧ c.time.val = tau),
    nativeGpreBoundaryContextTowerSource x c

/-- The corresponding real provenance readout before any camera compression. -/
def nativeGpreFiniteBoundaryRealReadoutAt
    (b tau : ℕ)
    (S : Finset NativeGpreBoundaryContext)
    (x : NativeGpreComplexEdgeCore) : ℝ :=
  ∑ c ∈ S.filter
      (fun c => c.towerPrime.val = b ∧ c.time.val = tau),
    (nativeGpreBoundaryValueLift x c).re

/-- Exact finite collapse identity: the common tower moment of the extracted
source is the complete real provenance readout on the selected fiber. -/
theorem inner_nativeGpreTowerProfileVector_finiteBoundaryTowerSourceAt
    (b tau : ℕ)
    (S : Finset NativeGpreBoundaryContext)
    (x : NativeGpreComplexEdgeCore) :
    inner ℝ (nativeGpreTowerProfileVector b tau)
        (nativeGpreFiniteBoundaryTowerSourceAt b tau S x) =
      nativeGpreFiniteBoundaryRealReadoutAt b tau S x := by
  classical
  unfold nativeGpreFiniteBoundaryTowerSourceAt
    nativeGpreFiniteBoundaryRealReadoutAt
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro c hc
  have hfiber := (Finset.mem_filter.mp hc).2
  rcases hfiber with ⟨hbase, htau⟩
  simpa [hbase, htau] using
    (inner_nativeGpreTowerProfileVector_boundaryContextTowerSource x c)

/-- Weighted finite source for an arbitrary context-dependent functional on one
material fiber. -/
noncomputable def nativeGpreFiniteWeightedBoundaryTowerSourceAt
    (b tau : ℕ)
    (S : Finset NativeGpreBoundaryContext)
    (weight : NativeGpreBoundaryContext → ℂ)
    (x : NativeGpreComplexEdgeCore) : NativeGpreTowerHilbert :=
  ∑ c ∈ S.filter
      (fun c => c.towerPrime.val = b ∧ c.time.val = tau),
    nativeGpreWeightedBoundaryContextTowerSource (weight c) x c

/-- The scalar functional read by the preceding weighted source. -/
def nativeGpreFiniteWeightedBoundaryRealReadoutAt
    (b tau : ℕ)
    (S : Finset NativeGpreBoundaryContext)
    (weight : NativeGpreBoundaryContext → ℂ)
    (x : NativeGpreComplexEdgeCore) : ℝ :=
  ∑ c ∈ S.filter
      (fun c => c.towerPrime.val = b ∧ c.time.val = tau),
    (weight c * nativeGpreBoundaryValueLift x c).re

/-- Every finite weighted provenance functional on one material fiber is a
literal moment of the explicitly extracted tower source. -/
theorem inner_nativeGpreTowerProfileVector_finiteWeightedBoundaryTowerSourceAt
    (b tau : ℕ)
    (S : Finset NativeGpreBoundaryContext)
    (weight : NativeGpreBoundaryContext → ℂ)
    (x : NativeGpreComplexEdgeCore) :
    inner ℝ (nativeGpreTowerProfileVector b tau)
        (nativeGpreFiniteWeightedBoundaryTowerSourceAt
          b tau S weight x) =
      nativeGpreFiniteWeightedBoundaryRealReadoutAt
        b tau S weight x := by
  classical
  unfold nativeGpreFiniteWeightedBoundaryTowerSourceAt
    nativeGpreFiniteWeightedBoundaryRealReadoutAt
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro c hc
  have hfiber := (Finset.mem_filter.mp hc).2
  rcases hfiber with ⟨hbase, htau⟩
  simpa [hbase, htau] using
    (inner_nativeGpreTowerProfileVector_weightedBoundaryContextTowerSource
      (weight c) x c)

/-- Zero weighting produces zero scalar readout on every finite base fiber. -/
@[simp] theorem nativeGpreFiniteWeightedBoundaryRealReadoutAt_zero
    (b tau : ℕ)
    (S : Finset NativeGpreBoundaryContext)
    (x : NativeGpreComplexEdgeCore) :
    nativeGpreFiniteWeightedBoundaryRealReadoutAt
      b tau S (fun _ => 0) x = 0 := by
  classical
  simp [nativeGpreFiniteWeightedBoundaryRealReadoutAt]

end

end CPFormal.Analytic.Cp
