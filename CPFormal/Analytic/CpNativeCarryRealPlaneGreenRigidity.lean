import CPFormal.Analytic.CpNativeCarryRealPlaneBracket

/-!
# Real-plane Green rigidity for the native carry boundary

The primitive carry camera already lives in `R x R`.  This module keeps the
operator-level rigidity in the same real carrier.

A real plane vector has two invariant pairings:

* the Euclidean dot product;
* the oriented area.

Together they retain exactly the information needed by the two-state Green
identity.  A conformal boundary slope acts by

`u |-> time * u + transverse * J u`,

where `J(x,y)=(-y,x)` is the real quarter-turn.  Green symmetry compares both
orientations of the real pairing.  On one nonzero characteristic direction it
forces `transverse = 0`; the tangential time remains arbitrary.

For the native carry parameterization the transverse coefficient is
`1/2 - sigma`.  Hence a real Green-symmetric realization of the bracket
boundary can close only at `sigma = 1/2`.

No non-real scalar field, imaginary unit, complex exponential, or zeta object
occurs in this module.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-! ## The oriented real pairing -/

/-- A counterclockwise quarter-turn in the native real plane. -/
def nativeCarryRealPlaneQuarterTurn
    (u : NativeCarryRealPlane) : NativeCarryRealPlane :=
  (-u.2, u.1)

/-- A real conformal slope: tangential motion plus transverse quarter-turn. -/
def nativeCarryRealPlaneConformalAction
    (time transverse : ℝ) (u : NativeCarryRealPlane) :
    NativeCarryRealPlane :=
  (time * u.1 - transverse * u.2,
    transverse * u.1 + time * u.2)

/--
The two real coordinates of the oriented pairing: Euclidean dot product and
oriented area.
-/
def nativeCarryRealPlaneOrientedPair
    (y x : NativeCarryRealPlane) : NativeCarryRealPlane :=
  (y.1 * x.1 + y.2 * x.2,
    y.1 * x.2 - y.2 * x.1)

@[simp] theorem nativeCarryRealPlaneOrientedPair_self
    (u : NativeCarryRealPlane) :
    nativeCarryRealPlaneOrientedPair u u =
      (nativeCarryRealPlaneEnergy u, 0) := by
  rcases u with ⟨x, y⟩
  apply Prod.ext <;>
    simp [nativeCarryRealPlaneOrientedPair,
      nativeCarryRealPlaneEnergy] <;>
    ring

/-- Lagrange's two-square identity for the real oriented pairing. -/
@[simp] theorem nativeCarryRealPlaneEnergy_orientedPair
    (y x : NativeCarryRealPlane) :
    nativeCarryRealPlaneEnergy
        (nativeCarryRealPlaneOrientedPair y x) =
      nativeCarryRealPlaneEnergy y * nativeCarryRealPlaneEnergy x := by
  rcases y with ⟨a, b⟩
  rcases x with ⟨c, d⟩
  simp [nativeCarryRealPlaneEnergy,
    nativeCarryRealPlaneOrientedPair]
  ring

/--
In one real plane, the full dot--area pairing of two nonzero vectors cannot
vanish.  This is the one-complex-dimensional obstruction used below.
-/
theorem nativeCarryRealPlaneOrientedPair_ne_zero
    {y x : NativeCarryRealPlane} (hy : y ≠ 0) (hx : x ≠ 0) :
    nativeCarryRealPlaneOrientedPair y x ≠ 0 := by
  intro hpair
  have henergy :
      nativeCarryRealPlaneEnergy
          (nativeCarryRealPlaneOrientedPair y x) = 0 := by
    rw [hpair]
    simp [nativeCarryRealPlaneEnergy]
  rw [nativeCarryRealPlaneEnergy_orientedPair] at henergy
  rcases mul_eq_zero.mp henergy with hyEnergy | hxEnergy
  · exact hy ((nativeCarryRealPlaneEnergy_eq_zero_iff y).1 hyEnergy)
  · exact hx ((nativeCarryRealPlaneEnergy_eq_zero_iff x).1 hxEnergy)

/-- The oriented pairing is real-bilinear in its first slot. -/
@[simp] theorem nativeCarryRealPlaneOrientedPair_smul_left
    (a : ℝ) (y x : NativeCarryRealPlane) :
    nativeCarryRealPlaneOrientedPair (a • y) x =
      a • nativeCarryRealPlaneOrientedPair y x := by
  rcases y with ⟨y₁, y₂⟩
  rcases x with ⟨x₁, x₂⟩
  apply Prod.ext <;>
    simp [nativeCarryRealPlaneOrientedPair] <;>
    ring

/-- The oriented pairing is real-bilinear in its second slot. -/
@[simp] theorem nativeCarryRealPlaneOrientedPair_smul_right
    (a : ℝ) (y x : NativeCarryRealPlane) :
    nativeCarryRealPlaneOrientedPair y (a • x) =
      a • nativeCarryRealPlaneOrientedPair y x := by
  rcases y with ⟨y₁, y₂⟩
  rcases x with ⟨x₁, x₂⟩
  apply Prod.ext <;>
    simp [nativeCarryRealPlaneOrientedPair] <;>
    ring

/-- With no transverse component, conformal action is real scalar action. -/
@[simp] theorem nativeCarryRealPlaneConformalAction_zero_transverse
    (time : ℝ) (u : NativeCarryRealPlane) :
    nativeCarryRealPlaneConformalAction time 0 u = time • u := by
  rcases u with ⟨x, y⟩
  simp [nativeCarryRealPlaneConformalAction]

/-- Acting in the first slot changes the oriented component by `-transverse`. -/
@[simp] theorem nativeCarryRealPlaneOrientedPair_conformalAction_left
    (time transverse : ℝ) (u : NativeCarryRealPlane) :
    nativeCarryRealPlaneOrientedPair
        (nativeCarryRealPlaneConformalAction time transverse u) u =
      (time * nativeCarryRealPlaneEnergy u,
        -transverse * nativeCarryRealPlaneEnergy u) := by
  rcases u with ⟨x, y⟩
  apply Prod.ext <;>
    simp [nativeCarryRealPlaneOrientedPair,
      nativeCarryRealPlaneConformalAction,
      nativeCarryRealPlaneEnergy] <;>
    ring

/-- Acting in the second slot changes the oriented component by `+transverse`. -/
@[simp] theorem nativeCarryRealPlaneOrientedPair_conformalAction_right
    (time transverse : ℝ) (u : NativeCarryRealPlane) :
    nativeCarryRealPlaneOrientedPair u
        (nativeCarryRealPlaneConformalAction time transverse u) =
      (time * nativeCarryRealPlaneEnergy u,
        transverse * nativeCarryRealPlaneEnergy u) := by
  rcases u with ⟨x, y⟩
  apply Prod.ext <;>
    simp [nativeCarryRealPlaneOrientedPair,
      nativeCarryRealPlaneConformalAction,
      nativeCarryRealPlaneEnergy] <;>
    ring

/-! ## A boundary pencil entirely over the reals -/

/-- Real value--flux pencil on the native two-coordinate boundary carrier. -/
structure NativeCarryRealBoundaryPencil
    (X : Type*) [AddCommGroup X] [Module ℝ X] where
  valueTrace : X →ₗ[ℝ] NativeCarryRealPlane
  fluxTrace : X →ₗ[ℝ] NativeCarryRealPlane

namespace NativeCarryRealBoundaryPencil

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

/-- Value--flux range of a real native carry pencil. -/
def relation (P : NativeCarryRealBoundaryPencil X) :
    Submodule ℝ (NativeCarryRealPlane × NativeCarryRealPlane) :=
  LinearMap.range (P.valueTrace.prod P.fluxTrace)

/-- The exact two-state Green identity, retaining dot and oriented area. -/
def SatisfiesGreenSymmetry
    (P : NativeCarryRealBoundaryPencil X) : Prop :=
  ∀ x y : X,
    nativeCarryRealPlaneOrientedPair
        (P.fluxTrace y) (P.valueTrace x) =
      nativeCarryRealPlaneOrientedPair
        (P.valueTrace y) (P.fluxTrace x)

/--
A characteristic direction whose real slope has a tangential coefficient and
a transverse quarter-turn coefficient.
-/
def RelationHasConformalSlope
    (P : NativeCarryRealBoundaryPencil X)
    (time transverse : ℝ) : Prop :=
  ∃ u : NativeCarryRealPlane, u ≠ 0 ∧
    (u, nativeCarryRealPlaneConformalAction time transverse u) ∈ P.relation

/--
The real Green identity kills the transverse coefficient of every nonzero
characteristic direction.  The tangential time is unrestricted.
-/
theorem relationHasConformalSlope_transverse_eq_zero
    (P : NativeCarryRealBoundaryPencil X)
    (hP : P.SatisfiesGreenSymmetry)
    {time transverse : ℝ}
    (hslope : P.RelationHasConformalSlope time transverse) :
    transverse = 0 := by
  rcases hslope with ⟨u, hu, hrelation⟩
  change
    (u, nativeCarryRealPlaneConformalAction time transverse u) ∈
      LinearMap.range (P.valueTrace.prod P.fluxTrace) at hrelation
  rcases hrelation with ⟨x, hx⟩
  have hvalue := congrArg Prod.fst hx
  have hflux := congrArg Prod.snd hx
  change P.valueTrace x = u at hvalue
  change P.fluxTrace x =
    nativeCarryRealPlaneConformalAction time transverse u at hflux
  have hgreen := hP x x
  rw [hvalue, hflux,
    nativeCarryRealPlaneOrientedPair_conformalAction_left,
    nativeCarryRealPlaneOrientedPair_conformalAction_right] at hgreen
  have horiented := congrArg Prod.snd hgreen
  have henergy : nativeCarryRealPlaneEnergy u ≠ 0 := by
    intro hzero
    exact hu ((nativeCarryRealPlaneEnergy_eq_zero_iff u).1 hzero)
  have hproduct :
      transverse * nativeCarryRealPlaneEnergy u = 0 := by
    linarith [horiented]
  exact (mul_eq_zero.mp hproduct).resolve_right henergy

/--
A Green-symmetric relation with boundary carrier equal to one real plane has
at most one conformal time.  The result is not a spectral rigidity theorem:
it is a dimension guardrail.  Distinct real characteristic times need
orthogonal directions in a larger boundary carrier.
-/
theorem relationHasConformalSlope_time_unique
    (P : NativeCarryRealBoundaryPencil X)
    (hP : P.SatisfiesGreenSymmetry)
    {time₁ transverse₁ time₂ transverse₂ : ℝ}
    (hslope₁ : P.RelationHasConformalSlope time₁ transverse₁)
    (hslope₂ : P.RelationHasConformalSlope time₂ transverse₂) :
    time₁ = time₂ := by
  have htransverse₁ : transverse₁ = 0 :=
    P.relationHasConformalSlope_transverse_eq_zero hP hslope₁
  have htransverse₂ : transverse₂ = 0 :=
    P.relationHasConformalSlope_transverse_eq_zero hP hslope₂
  rcases hslope₁ with ⟨u, hu, hrelation₁⟩
  rcases hslope₂ with ⟨v, hv, hrelation₂⟩
  change
    (u, nativeCarryRealPlaneConformalAction time₁ transverse₁ u) ∈
      LinearMap.range (P.valueTrace.prod P.fluxTrace) at hrelation₁
  change
    (v, nativeCarryRealPlaneConformalAction time₂ transverse₂ v) ∈
      LinearMap.range (P.valueTrace.prod P.fluxTrace) at hrelation₂
  rcases hrelation₁ with ⟨x, hx⟩
  rcases hrelation₂ with ⟨y, hy⟩
  have hxValue := congrArg Prod.fst hx
  have hxFlux := congrArg Prod.snd hx
  have hyValue := congrArg Prod.fst hy
  have hyFlux := congrArg Prod.snd hy
  change P.valueTrace x = u at hxValue
  change P.fluxTrace x =
    nativeCarryRealPlaneConformalAction time₁ transverse₁ u at hxFlux
  change P.valueTrace y = v at hyValue
  change P.fluxTrace y =
    nativeCarryRealPlaneConformalAction time₂ transverse₂ v at hyFlux
  have hgreen := hP x y
  rw [hxValue, hxFlux, hyValue, hyFlux,
    htransverse₁, htransverse₂,
    nativeCarryRealPlaneConformalAction_zero_transverse,
    nativeCarryRealPlaneConformalAction_zero_transverse,
    nativeCarryRealPlaneOrientedPair_smul_left,
    nativeCarryRealPlaneOrientedPair_smul_right] at hgreen
  let pairing := nativeCarryRealPlaneOrientedPair v u
  have hpairing : pairing ≠ 0 := by
    exact nativeCarryRealPlaneOrientedPair_ne_zero hv hu
  have hcoordinate : pairing.1 ≠ 0 ∨ pairing.2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hpairing
    exact Prod.ext h.1 h.2
  rcases hcoordinate with hfirst | hsecond
  · have hfirstEq := congrArg Prod.fst hgreen
    change time₂ * pairing.1 = time₁ * pairing.1 at hfirstEq
    have hproduct : (time₂ - time₁) * pairing.1 = 0 := by
      calc
        (time₂ - time₁) * pairing.1 =
            time₂ * pairing.1 - time₁ * pairing.1 := by ring
        _ = 0 := sub_eq_zero.mpr hfirstEq
    have htime : time₂ - time₁ = 0 :=
      (mul_eq_zero.mp hproduct).resolve_right hfirst
    linarith
  · have hsecondEq := congrArg Prod.snd hgreen
    change time₂ * pairing.2 = time₁ * pairing.2 at hsecondEq
    have hproduct : (time₂ - time₁) * pairing.2 = 0 := by
      calc
        (time₂ - time₁) * pairing.2 =
            time₂ * pairing.2 - time₁ * pairing.2 := by ring
        _ = 0 := sub_eq_zero.mpr hsecondEq
    have htime : time₂ - time₁ = 0 :=
      (mul_eq_zero.mp hproduct).resolve_right hsecond
    linarith

/-- Explicit no-go form of the preceding dimension guardrail. -/
theorem not_relationHasConformalSlope_of_distinct_time
    (P : NativeCarryRealBoundaryPencil X)
    (hP : P.SatisfiesGreenSymmetry)
    {time₁ transverse₁ time₂ transverse₂ : ℝ}
    (htime : time₁ ≠ time₂)
    (hslope₁ : P.RelationHasConformalSlope time₁ transverse₁) :
    ¬ P.RelationHasConformalSlope time₂ transverse₂ := by
  intro hslope₂
  exact htime
    (P.relationHasConformalSlope_time_unique hP hslope₁ hslope₂)

end NativeCarryRealBoundaryPencil

/-! ## Native real bracket closure and the fixed-pencil target -/

/-- Infinite closing condition of the primitive real camera at `(sigma,time)`. -/
def NativeCarryRealPlaneBoundaryClosesAt
    (sigma time : ℝ) : Prop :=
  Filter.Tendsto
    (fun M : ℕ =>
      nativeCarryRealPlaneFiniteChartAt 3 M sigma time)
    Filter.atTop (nhds 0)

/-- Real form of the remaining zero-rigidity target. -/
def NativeCarryRealPlaneZeroRigidity : Prop :=
  ∀ {sigma time : ℝ}, 0 < sigma → sigma < 1 →
    NativeCarryRealPlaneBoundaryClosesAt sigma time →
      sigma = (1 : ℝ) / 2

/--
A fixed real Green-symmetric realization of the primitive bracket boundary.
The pencil does not depend on `sigma` or `time`; only its characteristic
direction does.
-/
structure NativeCarryRealGreenSymmetricBoundaryPencilRealization
    (X : Type*) [AddCommGroup X] [Module ℝ X] where
  pencil : NativeCarryRealBoundaryPencil X
  green_symmetry : pencil.SatisfiesGreenSymmetry
  boundaryClosure_to_relationHasConformalSlope :
    ∀ {sigma time : ℝ}, 0 < sigma → sigma < 1 →
      NativeCarryRealPlaneBoundaryClosesAt sigma time →
        pencil.RelationHasConformalSlope time ((1 : ℝ) / 2 - sigma)

namespace NativeCarryRealGreenSymmetricBoundaryPencilRealization

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

/--
The one-plane realization would collapse every two closing spectral times to
the same real number.  This exposes why `NativeCarryRealPlane` is sufficient
for the local transverse calculation but too small for the global boundary
spectrum.
-/
theorem boundaryClosure_time_unique
    (R : NativeCarryRealGreenSymmetricBoundaryPencilRealization X)
    {sigma₁ time₁ sigma₂ time₂ : ℝ}
    (hsigma₁0 : 0 < sigma₁) (hsigma₁1 : sigma₁ < 1)
    (hsigma₂0 : 0 < sigma₂) (hsigma₂1 : sigma₂ < 1)
    (hclose₁ : NativeCarryRealPlaneBoundaryClosesAt sigma₁ time₁)
    (hclose₂ : NativeCarryRealPlaneBoundaryClosesAt sigma₂ time₂) :
    time₁ = time₂ := by
  apply R.pencil.relationHasConformalSlope_time_unique R.green_symmetry
  · exact R.boundaryClosure_to_relationHasConformalSlope
      hsigma₁0 hsigma₁1 hclose₁
  · exact R.boundaryClosure_to_relationHasConformalSlope
      hsigma₂0 hsigma₂1 hclose₂

/--
Once the real pre-compression boundary transport is constructed, Green
symmetry forces the native quadratic exponent with no non-real scalar layer.
-/
theorem zeroRigidity
    (R : NativeCarryRealGreenSymmetricBoundaryPencilRealization X) :
    NativeCarryRealPlaneZeroRigidity := by
  intro sigma time hsigma0 hsigma1 hclose
  have hslope :=
    R.boundaryClosure_to_relationHasConformalSlope
      hsigma0 hsigma1 hclose
  have htransverse :
      (1 : ℝ) / 2 - sigma = 0 :=
    R.pencil.relationHasConformalSlope_transverse_eq_zero
      R.green_symmetry hslope
  linarith

end NativeCarryRealGreenSymmetricBoundaryPencilRealization

end

end CPFormal.Analytic.Cp
