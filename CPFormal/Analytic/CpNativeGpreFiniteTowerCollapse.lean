import CPFormal.Analytic.CpNativeGprePrimeCarryContraction
import CPFormal.Analytic.CpNativeGpreTfvdAnalysis

/-!
# Finite material-tower collapse of native G_pre provenance

The native provenance coefficient already contains one distinguished material
factor

`nativeUnitMassTowerProfile p tau j = p^(-j*tau) / j`.

This module opens that factor before any prime-camera synthesis.  A single
provenance context therefore determines a literal vector in the common tower
Hilbert space: all non-tower arithmetic data form its coefficient and the
material level chooses its coordinate.

Taking the moment of that source vector against the native profile of the same
camera and arithmetic time recovers exactly the real part of the original
provenance value coordinate.  Summing over an arbitrary finite fiber gives a
finite tower source whose moment is the complete real provenance readout on
that fiber.

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
prescribed prime-camera moment. -/
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
    _ = (x c.cell).re *
        nativeGpreTowerCoordinateCoefficient (c.withRole .value) := by
      rw [nativeGpreTowerCoordinateCoefficient_eq_kernel_mul_profile]
      ring
    _ = (nativeGpreBoundaryValueLift x c).re := by
      rw [nativeGpreBoundaryValueLift_apply]
      simp

/-- Finite source obtained by collapsing precisely the contexts of one
material prime and one arithmetic time. -/
noncomputable def nativeGpreFiniteBoundaryTowerSourceAt
    (p tau : ℕ)
    (S : Finset NativeGpreBoundaryContext)
    (x : NativeGpreComplexEdgeCore) : NativeGpreTowerHilbert :=
  ∑ c in S.filter
      (fun c => c.towerPrime.val = p ∧ c.time.val = tau),
    nativeGpreBoundaryContextTowerSource x c

/-- The corresponding real provenance readout before any camera compression. -/
def nativeGpreFiniteBoundaryRealReadoutAt
    (p tau : ℕ)
    (S : Finset NativeGpreBoundaryContext)
    (x : NativeGpreComplexEdgeCore) : ℝ :=
  ∑ c in S.filter
      (fun c => c.towerPrime.val = p ∧ c.time.val = tau),
    (nativeGpreBoundaryValueLift x c).re

/-- Exact finite collapse identity: the common tower moment of the extracted
source is the complete real provenance readout on the selected fiber. -/
theorem inner_nativeGpreTowerProfileVector_finiteBoundaryTowerSourceAt
    (p tau : ℕ)
    (S : Finset NativeGpreBoundaryContext)
    (x : NativeGpreComplexEdgeCore) :
    inner ℝ (nativeGpreTowerProfileVector p tau)
        (nativeGpreFiniteBoundaryTowerSourceAt p tau S x) =
      nativeGpreFiniteBoundaryRealReadoutAt p tau S x := by
  classical
  unfold nativeGpreFiniteBoundaryTowerSourceAt
    nativeGpreFiniteBoundaryRealReadoutAt
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro c hc
  have hfiber := (Finset.mem_filter.mp hc).2
  rcases hfiber with ⟨hp, htau⟩
  simpa [hp, htau] using
    (inner_nativeGpreTowerProfileVector_boundaryContextTowerSource x c)

end

end CPFormal.Analytic.Cp
