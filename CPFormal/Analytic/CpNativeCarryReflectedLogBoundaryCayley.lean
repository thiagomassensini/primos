import CPFormal.Analytic.CpNativeCarryReflectedLogBoundarySymmetry

/-!
# Cayley realization of the reflected native log boundary

The direct/reflected oriented boundary form is converted to the standard
value--flux Green form by the fixed Cayley coordinates

`Gamma_0(a,b) = (a+b)/2`,
`Gamma_1(a,b) = (I/2) * (a-b)`.

The standard Green defect of these traces is exactly `-I/2` times the oriented
form from the reflected channel.  On the diagonal condition `a=b`, the flux is
zero and the value remains arbitrary.  The resulting boundary relation is the
graph of the zero operator on `C`, hence is self-adjoint in the existing
`Submodule.adjoint` sense.

This closes maximality of the fixed direct/reflected boundary condition.  It
does not yet prove that bracket closure puts the native log-wave in this
condition; that transport remains the final spectral bridge.
-/

open scoped ComplexConjugate InnerProduct

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Cayley value coordinate of the direct/reflected boundary pair. -/
def nativeCarryReflectedLogCayleyValue :
    NativeCarryReflectedLogBoundary →ₗ[ℂ] ℂ where
  toFun x := (x.1 + x.2) / 2
  map_add' x y := by
    change ((x.1 + y.1) + (x.2 + y.2)) / 2 =
      (x.1 + x.2) / 2 + (y.1 + y.2) / 2
    ring
  map_smul' c x := by
    change (c * x.1 + c * x.2) / 2 = c * ((x.1 + x.2) / 2)
    ring

/-- Cayley flux coordinate of the direct/reflected boundary pair. -/
def nativeCarryReflectedLogCayleyFlux :
    NativeCarryReflectedLogBoundary →ₗ[ℂ] ℂ where
  toFun x := (Complex.I / 2) * (x.1 - x.2)
  map_add' x y := by
    change (Complex.I / 2) *
        ((x.1 + y.1) - (x.2 + y.2)) =
      (Complex.I / 2) * (x.1 - x.2) +
        (Complex.I / 2) * (y.1 - y.2)
    ring
  map_smul' c x := by
    change (Complex.I / 2) * (c * x.1 - c * x.2) =
      c * ((Complex.I / 2) * (x.1 - x.2))
    ring

@[simp] theorem nativeCarryReflectedLogCayleyValue_apply
    (x : NativeCarryReflectedLogBoundary) :
    nativeCarryReflectedLogCayleyValue x = (x.1 + x.2) / 2 :=
  rfl

@[simp] theorem nativeCarryReflectedLogCayleyFlux_apply
    (x : NativeCarryReflectedLogBoundary) :
    nativeCarryReflectedLogCayleyFlux x =
      (Complex.I / 2) * (x.1 - x.2) :=
  rfl

/-- The fixed Cayley value--flux pencil on the doubled endpoint carrier. -/
def nativeCarryReflectedLogCayleyPencil :
    LinearBoundaryPencil NativeCarryReflectedLogBoundary ℂ where
  valueTrace := nativeCarryReflectedLogCayleyValue
  fluxTrace := nativeCarryReflectedLogCayleyFlux

/-- Cayley coordinates convert the oriented direct/reflected form into the
standard Green defect. -/
theorem nativeCarryReflectedLogCayley_greenDefect
    (x y : NativeCarryReflectedLogBoundary) :
    inner ℂ
          (nativeCarryReflectedLogCayleyPencil.fluxTrace y)
          (nativeCarryReflectedLogCayleyPencil.valueTrace x) -
        inner ℂ
          (nativeCarryReflectedLogCayleyPencil.valueTrace y)
          (nativeCarryReflectedLogCayleyPencil.fluxTrace x) =
      (-Complex.I / 2) *
        nativeCarryReflectedLogBoundaryForm y x := by
  simp [nativeCarryReflectedLogCayleyPencil,
    nativeCarryReflectedLogCayleyValue,
    nativeCarryReflectedLogCayleyFlux,
    nativeCarryReflectedLogBoundaryForm,
    RCLike.inner_apply]
  ring_nf

/-- The Cayley pencil restricted to the fixed reflected diagonal condition. -/
def nativeCarryReflectedLogDiagonalCayleyPencil :
    LinearBoundaryPencil nativeCarryReflectedLogDiagonal ℂ :=
  nativeCarryReflectedLogCayleyPencil.pullback
    nativeCarryReflectedLogDiagonal.subtype

@[simp] theorem nativeCarryReflectedLogDiagonalCayleyFlux_eq_zero
    (x : nativeCarryReflectedLogDiagonal) :
    nativeCarryReflectedLogDiagonalCayleyPencil.fluxTrace x = 0 := by
  change (Complex.I / 2) * (x.1.1 - x.1.2) = 0
  have hx : x.1.1 = x.1.2 := x.property
  rw [hx, sub_self, mul_zero]

@[simp] theorem nativeCarryReflectedLogDiagonalCayleyValue_eq
    (x : nativeCarryReflectedLogDiagonal) :
    nativeCarryReflectedLogDiagonalCayleyPencil.valueTrace x = x.1.1 := by
  change (x.1.1 + x.1.2) / 2 = x.1.1
  have hx : x.1.1 = x.1.2 := x.property
  rw [← hx]
  ring

/-- The restricted Cayley pencil satisfies the exact two-state Green identity. -/
theorem nativeCarryReflectedLogDiagonalCayley_greenSymmetry :
    LinearBoundaryPencil.SatisfiesGreenSymmetry
      nativeCarryReflectedLogDiagonalCayleyPencil := by
  intro x y
  rw [nativeCarryReflectedLogDiagonalCayleyFlux_eq_zero,
    nativeCarryReflectedLogDiagonalCayleyFlux_eq_zero]
  simp

/-- Standard zero-flux relation in the scalar boundary space. -/
def nativeCarryZeroFluxBoundaryRelation :
    Submodule ℂ (ℂ × ℂ) where
  carrier := {boundary | boundary.2 = 0}
  zero_mem' := rfl
  add_mem' := by
    intro x y hx hy
    change x.2 + y.2 = 0
    rw [hx, hy, add_zero]
  smul_mem' := by
    intro c x hx
    change c * x.2 = 0
    rw [hx, mul_zero]

@[simp] theorem mem_nativeCarryZeroFluxBoundaryRelation
    (boundary : ℂ × ℂ) :
    boundary ∈ nativeCarryZeroFluxBoundaryRelation ↔ boundary.2 = 0 :=
  Iff.rfl

/-- The restricted reflected Cayley relation is exactly the graph of zero. -/
theorem nativeCarryReflectedLogDiagonalCayley_relation_eq_zeroFlux :
    nativeCarryReflectedLogDiagonalCayleyPencil.relation =
      nativeCarryZeroFluxBoundaryRelation := by
  ext boundary
  constructor
  · intro hboundary
    change boundary ∈ LinearMap.range
      (nativeCarryReflectedLogDiagonalCayleyPencil.valueTrace.prod
        nativeCarryReflectedLogDiagonalCayleyPencil.fluxTrace) at hboundary
    rcases hboundary with ⟨x, rfl⟩
    rw [mem_nativeCarryZeroFluxBoundaryRelation]
    exact nativeCarryReflectedLogDiagonalCayleyFlux_eq_zero x
  · intro hboundary
    rw [mem_nativeCarryZeroFluxBoundaryRelation] at hboundary
    change boundary ∈ LinearMap.range
      (nativeCarryReflectedLogDiagonalCayleyPencil.valueTrace.prod
        nativeCarryReflectedLogDiagonalCayleyPencil.fluxTrace)
    let x : nativeCarryReflectedLogDiagonal :=
      ⟨(boundary.1, boundary.1), rfl⟩
    refine ⟨x, ?_⟩
    apply Prod.ext
    · change nativeCarryReflectedLogDiagonalCayleyPencil.valueTrace x = boundary.1
      simp [x]
    · change nativeCarryReflectedLogDiagonalCayleyPencil.fluxTrace x = boundary.2
      rw [nativeCarryReflectedLogDiagonalCayleyFlux_eq_zero, hboundary]

/-- The scalar zero-flux relation equals its symplectic adjoint. -/
theorem nativeCarryZeroFluxBoundaryRelation_isSelfAdjoint :
    NativeBoundaryRelationIsSelfAdjoint
      nativeCarryZeroFluxBoundaryRelation := by
  unfold NativeBoundaryRelationIsSelfAdjoint
  ext boundary
  constructor
  · intro hboundary
    rw [Submodule.mem_adjoint_iff] at hboundary
    rw [mem_nativeCarryZeroFluxBoundaryRelation]
    have htest := hboundary (1 : ℂ) 0 (by rfl)
    simpa [RCLike.inner_apply] using htest
  · intro hboundary
    rw [mem_nativeCarryZeroFluxBoundaryRelation] at hboundary
    rw [Submodule.mem_adjoint_iff]
    intro a b hab
    have hb : b = 0 := hab
    change inner ℂ b boundary.1 - inner ℂ a boundary.2 = 0
    rw [hb, hboundary]
    simp

/-- The fixed direct/reflected diagonal boundary relation is genuinely
self-adjoint after the Cayley transform. -/
theorem nativeCarryReflectedLogDiagonalCayley_relation_isSelfAdjoint :
    NativeBoundaryRelationIsSelfAdjoint
      nativeCarryReflectedLogDiagonalCayleyPencil.relation := by
  rw [nativeCarryReflectedLogDiagonalCayley_relation_eq_zeroFlux]
  exact nativeCarryZeroFluxBoundaryRelation_isSelfAdjoint

end

end CPFormal.Analytic.Cp
