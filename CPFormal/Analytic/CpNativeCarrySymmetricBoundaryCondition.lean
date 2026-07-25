import CPFormal.Analytic.CpNativeGpreHilbertGluedGreenDefect

/-!
# Symmetric boundary conditions for the native carry pencil

The native full-Hilbert boundary traces are already fixed:

`Gamma_0 x = (x 0, provenanceValue x)`,
`Gamma_1 x = (q^(-1) x 1 - x 0, provenanceNumberFlux x)`.

This module imposes an honest, parameter-independent boundary condition

`Gamma_1 x = T (Gamma_0 x)`

for one fixed symmetric boundary operator `T`.  The admitted state space is the
kernel of the linear map `Gamma_1 - T Gamma_0`; it is not defined through a
Genuine zero or through the desired spectral conclusion.

The Green identity then follows directly from symmetry of `T`.  Specializing to
the concrete TFVD--`G_pre` Hilbert pencil proves that every such domain is
pairwise isotropic for the exact vertical Wronskian.  This supplies the first
constructive half of the remaining operator gate: a large canonical family of
admissible symmetric domains.

The later log-phase realization must select the particular member of this
family whose characteristic slopes are the native carry resonance parameters.
-/

open scoped ComplexConjugate InnerProduct

namespace CPFormal.Analytic.Cp

noncomputable section

namespace LinearBoundaryPencil

variable {X B : Type*}
  [AddCommGroup X] [Module ℂ X]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B]

/-- States satisfying the fixed boundary condition `Gamma_1 = T Gamma_0`. -/
def boundaryConditionDomain
    (P : LinearBoundaryPencil X B) (T : B →ₗ[ℂ] B) : Submodule ℂ X :=
  LinearMap.ker (P.fluxTrace - T.comp P.valueTrace)

@[simp] theorem mem_boundaryConditionDomain
    (P : LinearBoundaryPencil X B) (T : B →ₗ[ℂ] B) (x : X) :
    x ∈ P.boundaryConditionDomain T ↔
      P.fluxTrace x = T (P.valueTrace x) := by
  rw [boundaryConditionDomain, LinearMap.mem_ker]
  change P.fluxTrace x - T (P.valueTrace x) = 0 ↔ _
  exact sub_eq_zero

/-- The native pencil restricted to one fixed boundary-condition domain. -/
def onBoundaryCondition
    (P : LinearBoundaryPencil X B) (T : B →ₗ[ℂ] B) :
    LinearBoundaryPencil (P.boundaryConditionDomain T) B :=
  P.pullback (P.boundaryConditionDomain T).subtype

@[simp] theorem onBoundaryCondition_valueTrace_apply
    (P : LinearBoundaryPencil X B) (T : B →ₗ[ℂ] B)
    (x : P.boundaryConditionDomain T) :
    (P.onBoundaryCondition T).valueTrace x = P.valueTrace (x : X) := rfl

@[simp] theorem onBoundaryCondition_fluxTrace_apply
    (P : LinearBoundaryPencil X B) (T : B →ₗ[ℂ] B)
    (x : P.boundaryConditionDomain T) :
    (P.onBoundaryCondition T).fluxTrace x = P.fluxTrace (x : X) := rfl

/-- A symmetric boundary operator makes its boundary-condition pencil satisfy
Green symmetry exactly. -/
theorem onBoundaryCondition_satisfiesGreenSymmetry
    (P : LinearBoundaryPencil X B) (T : B →ₗ[ℂ] B)
    (hT : T.IsSymmetric) :
    SatisfiesGreenSymmetry (P.onBoundaryCondition T) := by
  intro x y
  have hx : P.fluxTrace (x : X) = T (P.valueTrace (x : X)) :=
    (P.mem_boundaryConditionDomain T (x : X)).1 x.property
  have hy : P.fluxTrace (y : X) = T (P.valueTrace (y : X)) :=
    (P.mem_boundaryConditionDomain T (y : X)).1 y.property
  change
    inner ℂ (P.fluxTrace (y : X)) (P.valueTrace (x : X)) =
      inner ℂ (P.valueTrace (y : X)) (P.fluxTrace (x : X))
  rw [hy, hx]
  exact hT _ _

/-- Hence the range relation of every symmetric fixed boundary condition is a
symmetric linear relation. -/
theorem onBoundaryCondition_relation_isSymmetric
    (P : LinearBoundaryPencil X B) (T : B →ₗ[ℂ] B)
    (hT : T.IsSymmetric) :
    NativeBoundaryRelationIsSymmetric (P.onBoundaryCondition T).relation :=
  LinearBoundaryPencil.relation_isSymmetric_of_satisfiesGreenSymmetry
    (P.onBoundaryCondition T)
    (P.onBoundaryCondition_satisfiesGreenSymmetry T hT)

/-- Real scalar Robin operators form a canonical symmetric family on every
complex boundary Hilbert space. -/
def realScalarBoundaryOperator (a : ℝ) : B →ₗ[ℂ] B :=
  (a : ℂ) • LinearMap.id

/-- Multiplication by a real scalar is symmetric. -/
theorem realScalarBoundaryOperator_isSymmetric (a : ℝ) :
    (realScalarBoundaryOperator (B := B) a).IsSymmetric := by
  intro x y
  change inner ℂ ((a : ℂ) • x) y = inner ℂ x ((a : ℂ) • y)
  rw [inner_smul_left, inner_smul_right]
  simp

end LinearBoundaryPencil

/-! ## Specialization to the concrete full-Hilbert TFVD--G_pre pencil -/

/-- The concrete native carry domain selected by a fixed boundary operator. -/
abbrev nativeGpreHilbertBoundaryConditionDomain
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (T : NativeGpreHilbertGluedBoundary S →ₗ[ℂ]
      NativeGpreHilbertGluedBoundary S) :
    Submodule ℂ CarryVerticalL2 :=
  (nativeGpreHilbertGluedBoundaryPencil q S).boundaryConditionDomain T

/-- The concrete pencil restricted to the preceding fixed boundary condition. -/
abbrev nativeGpreHilbertBoundaryConditionPencil
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (T : NativeGpreHilbertGluedBoundary S →ₗ[ℂ]
      NativeGpreHilbertGluedBoundary S) :
    LinearBoundaryPencil (nativeGpreHilbertBoundaryConditionDomain q S T)
      (NativeGpreHilbertGluedBoundary S) :=
  (nativeGpreHilbertGluedBoundaryPencil q S).onBoundaryCondition T

/-- Every fixed symmetric boundary operator selects a pairwise
Wronskian-isotropic domain in the complete vertical carry Hilbert space. -/
theorem nativeGpreHilbertBoundaryConditionDomain_isotropic
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (T : NativeGpreHilbertGluedBoundary S →ₗ[ℂ]
      NativeGpreHilbertGluedBoundary S)
    (hT : T.IsSymmetric) :
    CarryVerticalBoundaryIsotropic q
      (nativeGpreHilbertBoundaryConditionDomain q S T) := by
  intro x y
  have hgreen :=
    LinearBoundaryPencil.onBoundaryCondition_satisfiesGreenSymmetry
      (nativeGpreHilbertGluedBoundaryPencil q S) T hT x y
  have hdefect :=
    nativeGpreHilbertGluedGreenDefect_eq_verticalWronskian
      q S (x : CarryVerticalL2) (y : CarryVerticalL2)
  change
    inner ℂ
        ((nativeGpreHilbertGluedBoundaryPencil q S).fluxTrace
          (y : CarryVerticalL2))
        ((nativeGpreHilbertGluedBoundaryPencil q S).valueTrace
          (x : CarryVerticalL2)) =
      inner ℂ
        ((nativeGpreHilbertGluedBoundaryPencil q S).valueTrace
          (y : CarryVerticalL2))
        ((nativeGpreHilbertGluedBoundaryPencil q S).fluxTrace
          (x : CarryVerticalL2))
    at hgreen
  rw [hgreen, sub_self] at hdefect
  exact hdefect.symm

/-- The corresponding concrete boundary relation is symmetric. -/
theorem nativeGpreHilbertBoundaryConditionRelation_isSymmetric
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (T : NativeGpreHilbertGluedBoundary S →ₗ[ℂ]
      NativeGpreHilbertGluedBoundary S)
    (hT : T.IsSymmetric) :
    NativeBoundaryRelationIsSymmetric
      (nativeGpreHilbertBoundaryConditionPencil q S T).relation :=
  LinearBoundaryPencil.onBoundaryCondition_relation_isSymmetric
    (nativeGpreHilbertGluedBoundaryPencil q S) T hT

/-- Real Robin boundary conditions give a concrete one-parameter family of
Wronskian-isotropic native carry domains. -/
theorem nativeGpreHilbert_realScalarBoundaryConditionDomain_isotropic
    (q : ℝ) (S : Finset NativeGpreBoundaryContext) (a : ℝ) :
    CarryVerticalBoundaryIsotropic q
      (nativeGpreHilbertBoundaryConditionDomain q S
        (LinearBoundaryPencil.realScalarBoundaryOperator
          (B := NativeGpreHilbertGluedBoundary S) a)) :=
  nativeGpreHilbertBoundaryConditionDomain_isotropic q S _
    (LinearBoundaryPencil.realScalarBoundaryOperator_isSymmetric
      (B := NativeGpreHilbertGluedBoundary S) a)

end

end CPFormal.Analytic.Cp
