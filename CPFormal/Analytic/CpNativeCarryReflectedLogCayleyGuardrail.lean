import CPFormal.Analytic.CpNativeCarryReflectedLogBoundaryCayley

/-!
# Guardrails for the reflected log Cayley boundary

This module records exactly what the already constructed Cayley relation does.
It is intentionally independent of bracket closure:

* the Cayley datum of a direct/reflected pair lies in the zero-flux relation
  exactly when the original pair is diagonal;
* for the native characteristic pair `(z, conj z)`, this is exactly the named
  reflected-flux matching condition;
* its Cayley flux is the transverse carry displacement;
* as a spectral relation, zero-flux has characteristic slope `0` only.

The last item prevents the zero-flux boundary condition from being mistaken for
the still-missing fixed spectral pencil whose characteristic parameter is `z`.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Cayley value--flux data of a direct/reflected endpoint pair. -/
def nativeCarryReflectedLogCayleyData
    (x : NativeCarryReflectedLogBoundary) : ℂ × ℂ :=
  (nativeCarryReflectedLogCayleyValue x,
    nativeCarryReflectedLogCayleyFlux x)

/-- The fixed zero-flux relation accepts exactly the original
direct/reflected diagonal. -/
theorem nativeCarryReflectedLogCayleyData_mem_zeroFlux_iff
    (x : NativeCarryReflectedLogBoundary) :
    nativeCarryReflectedLogCayleyData x ∈
        nativeCarryZeroFluxBoundaryRelation ↔
      x ∈ nativeCarryReflectedLogDiagonal := by
  rw [mem_nativeCarryZeroFluxBoundaryRelation,
    mem_nativeCarryReflectedLogDiagonal]
  change (Complex.I / 2) * (x.1 - x.2) = 0 ↔ x.1 = x.2
  constructor
  · intro hzero
    have hcoefficient : (Complex.I / 2 : ℂ) ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      norm_num at him
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hcoefficient)
  · intro hdiag
    rw [hdiag, sub_self, mul_zero]

/-- For the native characteristic direct/reflected flux, zero-flux Cayley
membership is exactly the already named matching condition. -/
theorem nativeCarryReflectedLogCharacteristicCayleyData_mem_zeroFlux_iff
    (z : ℂ) :
    nativeCarryReflectedLogCayleyData
          (nativeCarryReflectedLogBoundaryFlux z) ∈
        nativeCarryZeroFluxBoundaryRelation ↔
      NativeCarryReflectedLogFluxMatches z := by
  simpa [NativeCarryReflectedLogFluxMatches] using
    (nativeCarryReflectedLogCayleyData_mem_zeroFlux_iff
      (nativeCarryReflectedLogBoundaryFlux z))

/-- The same statement through the relation of the restricted Cayley pencil. -/
theorem nativeCarryReflectedLogCharacteristicCayleyData_mem_relation_iff
    (z : ℂ) :
    nativeCarryReflectedLogCayleyData
          (nativeCarryReflectedLogBoundaryFlux z) ∈
        nativeCarryReflectedLogDiagonalCayleyPencil.relation ↔
      NativeCarryReflectedLogFluxMatches z := by
  rw [nativeCarryReflectedLogDiagonalCayley_relation_eq_zeroFlux]
  exact
    nativeCarryReflectedLogCharacteristicCayleyData_mem_zeroFlux_iff z

/-- The Cayley flux of the characteristic pair is exactly the real transverse
carry displacement. -/
theorem nativeCarryReflectedLogCayleyFlux_boundaryFlux_eq_displacement
    (z : ℂ) :
    nativeCarryReflectedLogCayleyFlux
        (nativeCarryReflectedLogBoundaryFlux z) =
      ((criticalDisplacement
        (carryComplexTimeParameter z).re : ℝ) : ℂ) := by
  rw [criticalDisplacement_carryComplexTimeParameter_re,
    nativeCarryReflectedLogBoundaryFlux_eq]
  change (Complex.I / 2) * (z - (starRingEnd ℂ) z) =
    ((-z.im : ℝ) : ℂ)
  apply Complex.ext
  · simp
    ring
  · simp
    ring

/-- The raw zero-flux relation has one characteristic slope only: zero. -/
theorem nativeCarryZeroFluxBoundaryRelation_hasCharacteristicSlope_iff
    (z : ℂ) :
    NativeBoundaryRelationHasCharacteristicSlope
        nativeCarryZeroFluxBoundaryRelation z ↔
      z = 0 := by
  constructor
  · rintro ⟨u, hu, hmem⟩
    rw [mem_nativeCarryZeroFluxBoundaryRelation] at hmem
    change z * u = 0 at hmem
    exact (mul_eq_zero.mp hmem).resolve_right hu
  · intro hz
    subst z
    refine ⟨1, by norm_num, ?_⟩
    rw [mem_nativeCarryZeroFluxBoundaryRelation]
    simp

/-- Equivalently, the restricted Cayley pencil has `RelationHasSlope z` only
for `z = 0`.  It is a self-adjoint boundary condition, not yet the fixed
operator realization whose spectral parameter is native carry time. -/
theorem nativeCarryReflectedLogDiagonalCayley_relationHasSlope_iff
    (z : ℂ) :
    nativeCarryReflectedLogDiagonalCayleyPencil.RelationHasSlope z ↔
      z = 0 := by
  change NativeBoundaryRelationHasCharacteristicSlope
    nativeCarryReflectedLogDiagonalCayleyPencil.relation z ↔ z = 0
  rw [nativeCarryReflectedLogDiagonalCayley_relation_eq_zeroFlux]
  exact nativeCarryZeroFluxBoundaryRelation_hasCharacteristicSlope_iff z

/--
The proposed domain handoff stated literally: every closing bracket wave has
its characteristic Cayley datum in the fixed relation.
-/
def NativeCarryBracketClosureForcesCayleyRelationMembership : Prop :=
  ∀ {z : ℂ}, carryComplexTimeParameter z ∈ genuineCriticalStrip →
    NativeCarryLogWaveBoundaryCloses z →
      nativeCarryReflectedLogCayleyData
          (nativeCarryReflectedLogBoundaryFlux z) ∈
        nativeCarryReflectedLogDiagonalCayleyPencil.relation

/--
The preceding domain-membership handoff is exactly reflected-flux matching.
Merely renaming the missing transport as relation membership does not weaken
the open obligation.
-/
theorem nativeCarryBracketClosureForcesCayleyRelationMembership_iff :
    NativeCarryBracketClosureForcesCayleyRelationMembership ↔
      NativeCarryBracketClosureForcesReflectedLogFluxMatching := by
  constructor
  · intro hmembership z hz hclose
    exact
      (nativeCarryReflectedLogCharacteristicCayleyData_mem_relation_iff z).1
        (hmembership hz hclose)
  · intro hmatching z hz hclose
    exact
      (nativeCarryReflectedLogCharacteristicCayleyData_mem_relation_iff z).2
        (hmatching hz hclose)

/--
Consequently the Cayley relation-membership handoff is equivalent to the
existing complex-time zero-rigidity gate.
-/
theorem nativeCarryBracketClosureForcesCayleyRelationMembership_iff_zeroRigidity :
    NativeCarryBracketClosureForcesCayleyRelationMembership ↔
      NativeCarryComplexTimeZeroRigidity := by
  calc
    NativeCarryBracketClosureForcesCayleyRelationMembership ↔
        NativeCarryBracketClosureForcesReflectedLogFluxMatching :=
      nativeCarryBracketClosureForcesCayleyRelationMembership_iff
    _ ↔ NativeCarryComplexTimeZeroRigidity :=
      nativeCarryBracketClosureForcesReflectedLogFluxMatching_iff_zeroRigidity

end

end CPFormal.Analytic.Cp
