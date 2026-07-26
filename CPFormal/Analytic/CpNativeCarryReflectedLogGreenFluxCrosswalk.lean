import CPFormal.Analytic.CpNativeCarryReflectedLogBoundaryCayley
import CPFormal.Analytic.CpBracketGreenFlux

/-!
# Crosswalk between reflected log-boundary matching and coupled Green closure

The reflected Cayley boundary is now a fixed self-adjoint relation.  The only
remaining transport says that a closing bracket wave has direct/reflected
characteristic flux in the diagonal relation.

This module compares that statement with the previously isolated radial Green
gate.  The Lean kernel proves that the two are equivalent:

* bracket closure forces reflected flux matching;
* bracket closure forces the coupled Green flux to tend to zero.

Thus the self-adjoint reformulation identifies the correct boundary geometry,
but it does not hide or assume the final analytic transport.  It places the
old flux closure in the precise operator-theoretic location where it belongs.
-/

open scoped Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-- Bracket closure forces the already defined coupled Green flux to close. -/
def NativeCarryBracketClosureForcesCoupledGreenFluxClosure : Prop :=
  ∀ {z : ℂ}, carryComplexTimeParameter z ∈ genuineCriticalStrip →
    NativeCarryLogWaveBoundaryCloses z →
      Tendsto
        (fun M : ℕ =>
          finiteBracketCoupledCpGreenFlux 3 M
            (carryComplexTimeParameter z))
        atTop (nhds 0)

/-- Coupled Green closure and membership of the reflected characteristic flux in
the fixed diagonal self-adjoint boundary relation are the same remaining gate. -/
theorem nativeCarryBracketClosureForcesCoupledGreenFluxClosure_iff_reflectedFluxMatching :
    NativeCarryBracketClosureForcesCoupledGreenFluxClosure ↔
      NativeCarryBracketClosureForcesReflectedLogFluxMatching := by
  constructor
  · intro hflux z hz hboundary
    have hres :=
      (nativeCarryLogWaveBoundaryCloses_iff_resonance hz).1 hboundary
    have hzero :
        genuineContinuation (carryComplexTimeParameter z) = 0 := by
      simpa [IsNativeCarryComplexTimeResonance, carryComplexTimeGenuine] using hres
    have hcritical :=
      criticalDisplacement_eq_zero_of_coupledFlux_tendsto_zero
        3 (by norm_num) hz hzero (hflux hz hboundary)
    have him : z.im = 0 := by
      have hneg : -z.im = 0 := by
        simpa using hcritical
      linarith
    exact
      (nativeCarryReflectedLogFluxMatches_iff_im_eq_zero z).2 him
  · intro hmatching z hz hboundary
    have hres :=
      (nativeCarryLogWaveBoundaryCloses_iff_resonance hz).1 hboundary
    have hzero :
        genuineContinuation (carryComplexTimeParameter z) = 0 := by
      simpa [IsNativeCarryComplexTimeResonance, carryComplexTimeGenuine] using hres
    have him : z.im = 0 :=
      (nativeCarryReflectedLogFluxMatches_iff_im_eq_zero z).1
        (hmatching hz hboundary)
    have hcritical :
        criticalDisplacement (carryComplexTimeParameter z).re = 0 := by
      simp [him]
    exact finiteBracketCoupledCpGreenFlux_tendsto_zero_of_critical
      3 (by norm_num) hz hzero hcritical

/-- The coupled Green closure gate is exactly complex-time zero rigidity. -/
theorem nativeCarryBracketClosureForcesCoupledGreenFluxClosure_iff_zeroRigidity :
    NativeCarryBracketClosureForcesCoupledGreenFluxClosure ↔
      NativeCarryComplexTimeZeroRigidity := by
  calc
    NativeCarryBracketClosureForcesCoupledGreenFluxClosure ↔
        NativeCarryBracketClosureForcesReflectedLogFluxMatching :=
      nativeCarryBracketClosureForcesCoupledGreenFluxClosure_iff_reflectedFluxMatching
    _ ↔ NativeCarryComplexTimeZeroRigidity :=
      nativeCarryBracketClosureForcesReflectedLogFluxMatching_iff_zeroRigidity

/-- Consequently, coupled Green closure on bracket-closing native waves is
sufficient for the strong scalar theorem. -/
theorem genuineStrongNonvanishingInStrip_of_coupledGreenFluxClosure
    (hflux : NativeCarryBracketClosureForcesCoupledGreenFluxClosure) :
    GenuineStrongNonvanishingInStrip :=
  (nativeCarryComplexTimeZeroRigidity_iff_strongNonvanishing).1
    ((nativeCarryBracketClosureForcesCoupledGreenFluxClosure_iff_zeroRigidity).1
      hflux)

end

end CPFormal.Analytic.Cp
