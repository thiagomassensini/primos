import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Prod

/-!
# Canonical minimal-provenance quotient

Let `Q : X → Y` be a coarse readout and `A : X → Z` an analysis that
still sees part of the gauge erased by `Q`.  Quotienting by `ker Q` is then too
coarse whenever `A` is nonzero on that kernel.

The canonical repair does not choose a section, a pseudoinverse, or a preferred
representative.  It quotients only by the directions invisible to both maps:

`X / (ker Q ⊓ ker A)`.

This module proves that both maps descend, that this is the largest submodule
one may quotient out while retaining both readouts, and that the residual
gauge provenance is canonically the image of `ker Q` under `A` by the first
isomorphism theorem.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

universe u v w z

variable {R : Type u} [Field R]
variable {X : Type v} {Y : Type w} {Z : Type z}
variable [AddCommGroup X] [Module R X]
variable [AddCommGroup Y] [Module R Y]
variable [AddCommGroup Z] [Module R Z]

/-- Directions erased simultaneously by the coarse readout and the analysis. -/
def minimalProvenanceKernel
    (Q : X →ₗ[R] Y) (A : X →ₗ[R] Z) : Submodule R X :=
  LinearMap.ker Q ⊓ LinearMap.ker A

/-- The coarsest quotient that still retains both `Q` and `A`. -/
abbrev MinimalProvenanceCarrier
    (Q : X →ₗ[R] Y) (A : X →ₗ[R] Z) :=
  X ⧸ minimalProvenanceKernel Q A

/-- The joint readout whose kernel is the minimal-provenance kernel. -/
def minimalProvenanceJointMap
    (Q : X →ₗ[R] Y) (A : X →ₗ[R] Z) : X →ₗ[R] Y × Z :=
  Q.prod A

@[simp] theorem minimalProvenanceJointMap_apply
    (Q : X →ₗ[R] Y) (A : X →ₗ[R] Z) (x : X) :
    minimalProvenanceJointMap Q A x = (Q x, A x) :=
  rfl

/-- The joint map forgets exactly the directions invisible to both legs. -/
theorem ker_minimalProvenanceJointMap
    (Q : X →ₗ[R] Y) (A : X →ₗ[R] Z) :
    LinearMap.ker (minimalProvenanceJointMap Q A) =
      minimalProvenanceKernel Q A := by
  simp [minimalProvenanceJointMap, minimalProvenanceKernel,
    LinearMap.ker_prod]

/-- Canonical quotient map; it makes no choice of representatives. -/
def minimalProvenanceQuotientMap
    (Q : X →ₗ[R] Y) (A : X →ₗ[R] Z) :
    X →ₗ[R] MinimalProvenanceCarrier Q A :=
  (minimalProvenanceKernel Q A).mkQ

/-- The coarse readout descends to the enriched quotient. -/
def minimalProvenanceQ
    (Q : X →ₗ[R] Y) (A : X →ₗ[R] Z) :
    MinimalProvenanceCarrier Q A →ₗ[R] Y :=
  (minimalProvenanceKernel Q A).liftQ Q inf_le_left

/-- The analysis descends to the enriched quotient. -/
def minimalProvenanceA
    (Q : X →ₗ[R] Y) (A : X →ₗ[R] Z) :
    MinimalProvenanceCarrier Q A →ₗ[R] Z :=
  (minimalProvenanceKernel Q A).liftQ A inf_le_right

@[simp] theorem minimalProvenanceQ_mk
    (Q : X →ₗ[R] Y) (A : X →ₗ[R] Z) (x : X) :
    minimalProvenanceQ Q A
        (minimalProvenanceQuotientMap Q A x) = Q x :=
  rfl

@[simp] theorem minimalProvenanceA_mk
    (Q : X →ₗ[R] Y) (A : X →ₗ[R] Z) (x : X) :
    minimalProvenanceA Q A
        (minimalProvenanceQuotientMap Q A x) = A x :=
  rfl

/-- Both original maps factor through the same canonical quotient. -/
theorem minimalProvenance_factorization
    (Q : X →ₗ[R] Y) (A : X →ₗ[R] Z) :
    (minimalProvenanceQ Q A).comp
          (minimalProvenanceQuotientMap Q A) = Q ∧
      (minimalProvenanceA Q A).comp
          (minimalProvenanceQuotientMap Q A) = A := by
  constructor <;> ext x <;> rfl

/-- Any submodule that may be quotiented out while retaining both readouts is
contained in the minimal-provenance kernel.  Thus the construction is
canonical and maximally coarse. -/
theorem le_minimalProvenanceKernel_iff
    (Q : X →ₗ[R] Y) (A : X →ₗ[R] Z) (S : Submodule R X) :
    S ≤ minimalProvenanceKernel Q A ↔
      S ≤ LinearMap.ker Q ∧ S ≤ LinearMap.ker A := by
  exact le_inf_iff

/-- First-isomorphism realization of the enriched carrier as the range of the
joint readout `(Q,A)`. -/
noncomputable def minimalProvenanceEquivJointRange
    (Q : X →ₗ[R] Y) (A : X →ₗ[R] Z) :
    MinimalProvenanceCarrier Q A ≃ₗ[R]
      LinearMap.range (minimalProvenanceJointMap Q A) :=
  (Submodule.quotEquivOfEq
      (minimalProvenanceKernel Q A)
      (LinearMap.ker (minimalProvenanceJointMap Q A))
      (ker_minimalProvenanceJointMap Q A).symm).trans
    (minimalProvenanceJointMap Q A).quotKerEquivRange

@[simp] theorem minimalProvenanceEquivJointRange_mk
    (Q : X →ₗ[R] Y) (A : X →ₗ[R] Z) (x : X) :
    ((minimalProvenanceEquivJointRange Q A
        (minimalProvenanceQuotientMap Q A x) :
          LinearMap.range (minimalProvenanceJointMap Q A)) : Y × Z) =
      (Q x, A x) := by
  change
    (((minimalProvenanceJointMap Q A).quotKerEquivRange
        (Submodule.Quotient.mk x) :
          LinearMap.range (minimalProvenanceJointMap Q A)) : Y × Z) =
      (Q x, A x)
  rw [LinearMap.quotKerEquivRange_apply_mk]
  rfl

/-- Restriction of `A` to the gauge erased by `Q`. -/
def provenanceGaugeMap
    (Q : X →ₗ[R] Y) (A : X →ₗ[R] Z) :
    LinearMap.ker Q →ₗ[R] Z :=
  A.domRestrict (LinearMap.ker Q)

/-- The kernel of the restricted gauge map is precisely the part of
`ker Q ⊓ ker A` seen inside `ker Q`. -/
theorem mem_ker_provenanceGaugeMap_iff
    (Q : X →ₗ[R] Y) (A : X →ₗ[R] Z) (x : LinearMap.ker Q) :
    x ∈ LinearMap.ker (provenanceGaugeMap Q A) ↔
      (x : X) ∈ minimalProvenanceKernel Q A := by
  simp [provenanceGaugeMap, minimalProvenanceKernel,
    LinearMap.mem_ker]

/-- The residual gauge quotient is canonically equivalent to the image
`A(ker Q)`.  This is the precise provenance forgotten by the old quotient. -/
noncomputable def provenanceGaugeQuotientEquivImage
    (Q : X →ₗ[R] Y) (A : X →ₗ[R] Z) :
    (LinearMap.ker Q ⧸ LinearMap.ker (provenanceGaugeMap Q A)) ≃ₗ[R]
      LinearMap.range (provenanceGaugeMap Q A) :=
  (provenanceGaugeMap Q A).quotKerEquivRange

@[simp] theorem provenanceGaugeQuotientEquivImage_mk
    (Q : X →ₗ[R] Y) (A : X →ₗ[R] Z) (x : LinearMap.ker Q) :
    ((provenanceGaugeQuotientEquivImage Q A
        (Submodule.Quotient.mk x) :
          LinearMap.range (provenanceGaugeMap Q A)) : Z) = A x := by
  rfl

/-- Membership description of `A(ker Q)` without any chosen preimage. -/
theorem mem_provenanceGaugeImage_iff
    (Q : X →ₗ[R] Y) (A : X →ₗ[R] Z) (z : Z) :
    z ∈ LinearMap.range (provenanceGaugeMap Q A) ↔
      ∃ x : X, Q x = 0 ∧ A x = z := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.property, rfl⟩
  · rintro ⟨x, hxQ, rfl⟩
    exact ⟨⟨x, hxQ⟩, rfl⟩

/-! ## Canonical short exact sequence -/

/-- The residual gauge quotient appearing as the fiber of the descended
coarse readout. -/
abbrev MinimalProvenanceGaugeFiber
    (Q : X →ₗ[R] Y) (A : X →ₗ[R] Z) :=
  LinearMap.ker Q ⧸ LinearMap.ker (provenanceGaugeMap Q A)

/-- A gauge direction is sent to its class in the joint quotient. -/
def provenanceGaugeToCarrier
    (Q : X →ₗ[R] Y) (A : X →ₗ[R] Z) :
    LinearMap.ker Q →ₗ[R] MinimalProvenanceCarrier Q A :=
  (minimalProvenanceQuotientMap Q A).comp
    (LinearMap.ker Q).subtype

/-- The only gauge directions killed in the joint carrier are those also
invisible to `A`. -/
theorem ker_provenanceGaugeToCarrier
    (Q : X →ₗ[R] Y) (A : X →ₗ[R] Z) :
    LinearMap.ker (provenanceGaugeToCarrier Q A) =
      LinearMap.ker (provenanceGaugeMap Q A) := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  change
    (minimalProvenanceKernel Q A).mkQ (x : X) = 0 ↔ A x = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hx
    exact LinearMap.mem_ker.mp hx.2
  · intro hx
    exact ⟨x.property, LinearMap.mem_ker.mpr hx⟩

/-- Canonical inclusion of the residual gauge quotient into the joint
carrier.  It is induced by the original inclusion `ker Q ↪ X`; no section of
`Q` occurs. -/
def minimalProvenanceGaugeFiberInclusion
    (Q : X →ₗ[R] Y) (A : X →ₗ[R] Z) :
    MinimalProvenanceGaugeFiber Q A →ₗ[R]
      MinimalProvenanceCarrier Q A :=
  (LinearMap.ker (provenanceGaugeMap Q A)).liftQ
    (provenanceGaugeToCarrier Q A)
    (ker_provenanceGaugeToCarrier Q A).ge

/-- The gauge-fiber map is injective. -/
theorem minimalProvenanceGaugeFiberInclusion_injective
    (Q : X →ₗ[R] Y) (A : X →ₗ[R] Z) :
    Function.Injective (minimalProvenanceGaugeFiberInclusion Q A) := by
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot'
    (LinearMap.ker (provenanceGaugeMap Q A))
    (provenanceGaugeToCarrier Q A)
    (ker_provenanceGaugeToCarrier Q A).symm

/-- Descended coarse readout with its codomain restricted to the actual range
of `Q`. -/
def minimalProvenanceQRange
    (Q : X →ₗ[R] Y) (A : X →ₗ[R] Z) :
    MinimalProvenanceCarrier Q A →ₗ[R] LinearMap.range Q :=
  (minimalProvenanceKernel Q A).liftQ Q.rangeRestrict (by
    intro x hx
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    exact LinearMap.mem_ker.mp hx.1)

@[simp] theorem minimalProvenanceQRange_mk
    (Q : X →ₗ[R] Y) (A : X →ₗ[R] Z) (x : X) :
    minimalProvenanceQRange Q A
        (minimalProvenanceQuotientMap Q A x) = Q.rangeRestrict x :=
  rfl

/-- The descended coarse readout is onto its range. -/
theorem minimalProvenanceQRange_surjective
    (Q : X →ₗ[R] Y) (A : X →ₗ[R] Z) :
    Function.Surjective (minimalProvenanceQRange Q A) := by
  intro y
  rcases y.property with ⟨x, hx⟩
  refine ⟨minimalProvenanceQuotientMap Q A x, ?_⟩
  apply Subtype.ext
  simpa using hx

/-- Exactness at the joint carrier: the kernel of the descended `Q` is exactly
the embedded residual provenance fiber. -/
theorem range_minimalProvenanceGaugeFiberInclusion_eq_ker_QRange
    (Q : X →ₗ[R] Y) (A : X →ₗ[R] Z) :
    LinearMap.range (minimalProvenanceGaugeFiberInclusion Q A) =
      LinearMap.ker (minimalProvenanceQRange Q A) := by
  apply le_antisymm
  · rintro u ⟨v, rfl⟩
    obtain ⟨x, rfl⟩ :=
      Submodule.mkQ_surjective
        (LinearMap.ker (provenanceGaugeMap Q A)) v
    rw [LinearMap.mem_ker]
    change Q.rangeRestrict (x : X) = 0
    apply Subtype.ext
    exact x.property
  · intro u hu
    obtain ⟨x, rfl⟩ :=
      Submodule.mkQ_surjective (minimalProvenanceKernel Q A) u
    have hxQ : Q x = 0 := by
      have hzero := LinearMap.mem_ker.mp hu
      exact congrArg Subtype.val hzero
    let gauge : LinearMap.ker Q := ⟨x, hxQ⟩
    refine ⟨(Submodule.mkQ
      (LinearMap.ker (provenanceGaugeMap Q A))) gauge, ?_⟩
    rfl

end

end CPFormal.Analytic.Cp
