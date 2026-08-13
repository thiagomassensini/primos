import CPFormal.Analytic.CpNativeCarryRealPlaneGreenRigidity

/-!
# Infinite real spectral carrier for the native carry boundary

The local transverse calculation in `CpNativeCarryRealPlaneGreenRigidity`
uses one copy of `R x R`.  That copy is exactly large enough to retain energy
and oriented area, but it is too small to carry more than one real
characteristic time.

This module separates the two roles:

* every spectral coordinate still has the primitive real plane;
* the global boundary carrier is a family of such planes indexed by spectral
  time.

The fixed multiplication pencil

`(A u)(r) = r * u(r)`

is Green-symmetric coordinatewise and has a nonzero characteristic direction
at every real time.  Thus the real formulation has enough room for a genuine
spectrum without introducing a non-real scalar field.

The transverse rigidity proof remains local: if one nonzero family direction
has slope

`time * u + transverse * J u`,

coordinatewise Green symmetry forces `transverse = 0`.

Finally, the module distinguishes two boundary statements:

* an admissible closing state already preserves the quadratic carry mass, so
  it enters the fixed time-multiplication relation unconditionally;
* proving that every raw scalar bracket closure is admissible is exactly the
  still-open zero-rigidity bridge.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-! ## Spectral families of primitive real planes -/

/-- One primitive real plane at every spectral label. -/
abbrev NativeCarryRealPlaneFamily (ι : Type*) :=
  ι → NativeCarryRealPlane

/-- Conformal action applied independently in every spectral fiber. -/
def nativeCarryRealPlaneFamilyConformalAction
    {ι : Type*} (time transverse : ℝ)
    (u : NativeCarryRealPlaneFamily ι) :
    NativeCarryRealPlaneFamily ι :=
  fun i => nativeCarryRealPlaneConformalAction time transverse (u i)

/-- Dot--area pairing retained independently in every spectral fiber. -/
def nativeCarryRealPlaneFamilyOrientedPair
    {ι : Type*}
    (y x : NativeCarryRealPlaneFamily ι) :
    NativeCarryRealPlaneFamily ι :=
  fun i => nativeCarryRealPlaneOrientedPair (y i) (x i)

/-- A value--flux pencil whose boundary values are real-plane families. -/
structure NativeCarryRealPlaneFamilyBoundaryPencil
    (ι X : Type*) [AddCommGroup X] [Module ℝ X] where
  valueTrace : X →ₗ[ℝ] NativeCarryRealPlaneFamily ι
  fluxTrace : X →ₗ[ℝ] NativeCarryRealPlaneFamily ι

namespace NativeCarryRealPlaneFamilyBoundaryPencil

variable {ι X : Type*} [AddCommGroup X] [Module ℝ X]

/-- Value--flux range in the spectral-family boundary carrier. -/
def relation (P : NativeCarryRealPlaneFamilyBoundaryPencil ι X) :
    Submodule ℝ
      (NativeCarryRealPlaneFamily ι × NativeCarryRealPlaneFamily ι) :=
  LinearMap.range (P.valueTrace.prod P.fluxTrace)

/-- Coordinatewise real Green symmetry, retaining energy and oriented area. -/
def SatisfiesGreenSymmetry
    (P : NativeCarryRealPlaneFamilyBoundaryPencil ι X) : Prop :=
  ∀ x y : X,
    nativeCarryRealPlaneFamilyOrientedPair
        (P.fluxTrace y) (P.valueTrace x) =
      nativeCarryRealPlaneFamilyOrientedPair
        (P.valueTrace y) (P.fluxTrace x)

/-- A nonzero family direction with one global conformal slope. -/
def RelationHasConformalSlope
    (P : NativeCarryRealPlaneFamilyBoundaryPencil ι X)
    (time transverse : ℝ) : Prop :=
  ∃ u : NativeCarryRealPlaneFamily ι, u ≠ 0 ∧
    (u, nativeCarryRealPlaneFamilyConformalAction time transverse u) ∈
      P.relation

/--
The same Green argument as in one real plane kills the transverse coefficient.
Only one nonzero spectral fiber is needed; other characteristic times may live
in disjoint fibers.
-/
theorem relationHasConformalSlope_transverse_eq_zero
    (P : NativeCarryRealPlaneFamilyBoundaryPencil ι X)
    (hP : P.SatisfiesGreenSymmetry)
    {time transverse : ℝ}
    (hslope : P.RelationHasConformalSlope time transverse) :
    transverse = 0 := by
  rcases hslope with ⟨u, hu, hrelation⟩
  change
    (u, nativeCarryRealPlaneFamilyConformalAction time transverse u) ∈
      LinearMap.range (P.valueTrace.prod P.fluxTrace) at hrelation
  rcases hrelation with ⟨x, hx⟩
  have hvalue := congrArg Prod.fst hx
  have hflux := congrArg Prod.snd hx
  change P.valueTrace x = u at hvalue
  change P.fluxTrace x =
    nativeCarryRealPlaneFamilyConformalAction time transverse u at hflux
  have hgreen := hP x x
  rw [hvalue, hflux] at hgreen
  have hactive : ∃ i : ι, u i ≠ 0 := by
    by_contra h
    push Not at h
    apply hu
    funext i
    exact h i
  rcases hactive with ⟨i, hi⟩
  have hfiber := congrFun hgreen i
  change
    nativeCarryRealPlaneOrientedPair
        (nativeCarryRealPlaneConformalAction time transverse (u i)) (u i) =
      nativeCarryRealPlaneOrientedPair
        (u i)
        (nativeCarryRealPlaneConformalAction time transverse (u i))
    at hfiber
  rw [nativeCarryRealPlaneOrientedPair_conformalAction_left,
    nativeCarryRealPlaneOrientedPair_conformalAction_right] at hfiber
  have horiented := congrArg Prod.snd hfiber
  have henergy : nativeCarryRealPlaneEnergy (u i) ≠ 0 := by
    intro hzero
    exact hi ((nativeCarryRealPlaneEnergy_eq_zero_iff (u i)).1 hzero)
  have hproduct :
      transverse * nativeCarryRealPlaneEnergy (u i) = 0 := by
    linarith [horiented]
  exact (mul_eq_zero.mp hproduct).resolve_right henergy

end NativeCarryRealPlaneFamilyBoundaryPencil

/-! ## A fixed real pencil with every real time as a characteristic slope -/

/-- Pointwise multiplication by the real spectral label. -/
def nativeCarryRealTimeMultiplication :
    NativeCarryRealPlaneFamily ℝ →ₗ[ℝ] NativeCarryRealPlaneFamily ℝ where
  toFun u := fun r => r • u r
  map_add' u v := by
    funext r
    simp [smul_add]
  map_smul' a u := by
    funext r
    simp [smul_smul, mul_comm]

@[simp] theorem nativeCarryRealTimeMultiplication_apply
    (u : NativeCarryRealPlaneFamily ℝ) (r : ℝ) :
    nativeCarryRealTimeMultiplication u r = r • u r := rfl

/-- Fixed coordinate-multiplication pencil on the real spectral carrier. -/
def nativeCarryRealTimeMultiplicationBoundaryPencil :
    NativeCarryRealPlaneFamilyBoundaryPencil ℝ
      (NativeCarryRealPlaneFamily ℝ) where
  valueTrace := LinearMap.id
  fluxTrace := nativeCarryRealTimeMultiplication

@[simp] theorem nativeCarryRealTimeMultiplicationBoundaryPencil_value
    (u : NativeCarryRealPlaneFamily ℝ) :
    nativeCarryRealTimeMultiplicationBoundaryPencil.valueTrace u = u := rfl

@[simp] theorem nativeCarryRealTimeMultiplicationBoundaryPencil_flux
    (u : NativeCarryRealPlaneFamily ℝ) (r : ℝ) :
    nativeCarryRealTimeMultiplicationBoundaryPencil.fluxTrace u r =
      r • u r := rfl

/-- The fixed time-multiplication pencil is Green-symmetric in every fiber. -/
theorem nativeCarryRealTimeMultiplicationBoundaryPencil_greenSymmetry :
    nativeCarryRealTimeMultiplicationBoundaryPencil.SatisfiesGreenSymmetry := by
  intro x y
  funext r
  change
    nativeCarryRealPlaneOrientedPair (r • y r) (x r) =
      nativeCarryRealPlaneOrientedPair (y r) (r • x r)
  rw [nativeCarryRealPlaneOrientedPair_smul_left,
    nativeCarryRealPlaneOrientedPair_smul_right]

/--
Every real time occurs as a nonzero characteristic direction of the same fixed
real pencil.  The witness is supported only at that spectral label.
-/
theorem nativeCarryRealTimeMultiplicationBoundaryPencil_relationHasSlope
    (time : ℝ) :
    nativeCarryRealTimeMultiplicationBoundaryPencil.RelationHasConformalSlope
      time 0 := by
  classical
  let u : NativeCarryRealPlaneFamily ℝ :=
    fun r => if r = time then ((1 : ℝ), (0 : ℝ)) else 0
  have hu : u ≠ 0 := by
    intro hzero
    have hatTime := congrFun hzero time
    simp [u] at hatTime
  refine ⟨u, hu, ?_⟩
  change
    (u, nativeCarryRealPlaneFamilyConformalAction time 0 u) ∈
      LinearMap.range
        (nativeCarryRealTimeMultiplicationBoundaryPencil.valueTrace.prod
          nativeCarryRealTimeMultiplicationBoundaryPencil.fluxTrace)
  refine ⟨u, ?_⟩
  apply Prod.ext
  · rfl
  · funext r
    by_cases hr : r = time
    · subst r
      simp [nativeCarryRealPlaneFamilyConformalAction, u]
    · simp [nativeCarryRealPlaneFamilyConformalAction, u, hr]

/-! ## Mass balance and raw boundary closure -/

/--
The conjunction of quadratic mass balance and raw boundary closure. This is
not a distinct kind of zero; each conjunct retains its own meaning.
-/
def NativeCarryRealPlaneMassBalancedBoundaryClosesAt
    (sigma time : ℝ) : Prop :=
  NativeCarryRealPlaneMassCompatible sigma time ∧
    NativeCarryRealPlaneBoundaryClosesAt sigma time

/-- Mass balance fixes the radial exponent independently of closure. -/
theorem nativeCarryRealPlaneMassBalancedBoundaryClosesAt_sigma_eq_half
    {sigma time : ℝ}
    (hclose : NativeCarryRealPlaneMassBalancedBoundaryClosesAt sigma time) :
    sigma = (1 : ℝ) / 2 :=
  (nativeCarryRealPlaneMassCompatible_iff sigma time).1 hclose.1

/--
Mass balance together with closure enters the fixed infinite real pencil with
transverse coefficient `1/2 - sigma`.
-/
theorem massBalancedBoundaryClosure_to_timeMultiplicationRelationHasConformalSlope
    {sigma time : ℝ}
    (hclose : NativeCarryRealPlaneMassBalancedBoundaryClosesAt sigma time) :
    nativeCarryRealTimeMultiplicationBoundaryPencil.RelationHasConformalSlope
      time ((1 : ℝ) / 2 - sigma) := by
  have hsigma :=
    nativeCarryRealPlaneMassBalancedBoundaryClosesAt_sigma_eq_half hclose
  have htransverse : (1 : ℝ) / 2 - sigma = 0 := by
    linarith
  rw [htransverse]
  exact
    nativeCarryRealTimeMultiplicationBoundaryPencil_relationHasSlope time

/-- Exact raw-to-physical mass bridge left after scalar compression. -/
def NativeCarryRealPlaneBoundaryClosurePreservesMass : Prop :=
  ∀ {sigma time : ℝ}, 0 < sigma → sigma < 1 →
    NativeCarryRealPlaneBoundaryClosesAt sigma time →
      NativeCarryRealPlaneMassCompatible sigma time

/--
For the corrected infinite carrier, activating the fixed Green relation from
every raw boundary closure is exactly preservation of the carry mass.
-/
def NativeCarryRealPlaneBoundaryClosureActivatesTimePencil : Prop :=
  ∀ {sigma time : ℝ}, 0 < sigma → sigma < 1 →
    NativeCarryRealPlaneBoundaryClosesAt sigma time →
      nativeCarryRealTimeMultiplicationBoundaryPencil.RelationHasConformalSlope
        time ((1 : ℝ) / 2 - sigma)

/-- Raw scalar closure preserves mass exactly when it already has zero rigidity. -/
theorem nativeCarryRealPlaneBoundaryClosurePreservesMass_iff_zeroRigidity :
    NativeCarryRealPlaneBoundaryClosurePreservesMass ↔
      NativeCarryRealPlaneZeroRigidity := by
  constructor
  · intro hpreserves sigma time hsigma0 hsigma1 hclose
    exact (nativeCarryRealPlaneMassCompatible_iff sigma time).1
      (hpreserves hsigma0 hsigma1 hclose)
  · intro hrigid sigma time hsigma0 hsigma1 hclose
    exact (nativeCarryRealPlaneMassCompatible_iff sigma time).2
      (hrigid hsigma0 hsigma1 hclose)

/--
The desired activation of the corrected fixed time pencil is equivalent to
the raw mass bridge.  This theorem prevents the carrier correction from being
mistaken for a proof that scalar compression preserved the state.
-/
theorem nativeCarryRealPlaneBoundaryClosureActivatesTimePencil_iff_preservesMass :
    NativeCarryRealPlaneBoundaryClosureActivatesTimePencil ↔
      NativeCarryRealPlaneBoundaryClosurePreservesMass := by
  constructor
  · intro hactivates sigma time hsigma0 hsigma1 hclose
    have hslope := hactivates hsigma0 hsigma1 hclose
    have htransverse :
        (1 : ℝ) / 2 - sigma = 0 :=
      NativeCarryRealPlaneFamilyBoundaryPencil.relationHasConformalSlope_transverse_eq_zero
        nativeCarryRealTimeMultiplicationBoundaryPencil
        nativeCarryRealTimeMultiplicationBoundaryPencil_greenSymmetry
        hslope
    apply (nativeCarryRealPlaneMassCompatible_iff sigma time).2
    linarith
  · intro hpreserves sigma time hsigma0 hsigma1 hclose
    exact
      massBalancedBoundaryClosure_to_timeMultiplicationRelationHasConformalSlope
        ⟨hpreserves hsigma0 hsigma1 hclose, hclose⟩

/-- Consequently the corrected activation arrow is the exact zero-rigidity gate. -/
theorem nativeCarryRealPlaneBoundaryClosureActivatesTimePencil_iff_zeroRigidity :
    NativeCarryRealPlaneBoundaryClosureActivatesTimePencil ↔
      NativeCarryRealPlaneZeroRigidity := by
  rw [nativeCarryRealPlaneBoundaryClosureActivatesTimePencil_iff_preservesMass,
    nativeCarryRealPlaneBoundaryClosurePreservesMass_iff_zeroRigidity]

end

end CPFormal.Analytic.Cp
