import CPFormal.Analytic.CpNativeCarryRealPlaneGreenRigidity
import CPFormal.Analytic.CpNativeCarryRealSpectralBoundaryCarrier

/-!
# Exact confinement of the native real carry operator

The native operator is assembled in the order fixed by the carry geometry:

* the uncompressed real state must reproduce the inverse carry mass;
* a camera applies the additive saturated bracket to that state;
* a zero is a closing sequence of finite real resultants.

The camera width is arbitrary.  No primality assumption and no non-real
spectral parameter occur in this definition.

The main theorem identifies the full zero set of every such camera:

`native zero at (sigma,time)`

if and only if

`sigma = 1/2` and `native resonance at time`.

Thus the radial coordinate is not selected by cancellation after the bracket.
It is already the unique quadratic shell admitted by the native operator,
while the real time remains the only variable seen by the bracket closure.
-/

open scoped Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/--
Boundary closure of an arbitrary real saturated camera at radial presentation
`sigma` and real phase time `time`.
-/
def NativeCarryRealOperatorBoundaryClosesAt
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  Tendsto
    (fun cutoff : ℕ =>
      nativeCarryRealPlaneFiniteChartAt camera cutoff sigma time)
    atTop (nhds 0)

/--
A native resonance is boundary closure after the quadratic carry shell has
already been fixed.  Its only free spectral coordinate is real time.
-/
def IsNativeCarryRealOperatorResonance
    (camera : ℕ) (time : ℝ) : Prop :=
  NativeCarryRealOperatorBoundaryClosesAt
    camera ((1 : ℝ) / 2) time

/--
A zero presentation of the native real operator retains both pieces of its
construction: the pre-bracket carry mass law and the closing bracket
resultants.

Mass compatibility is part of the operator domain, not an additional bridge
from a compressed scalar zero.
-/
def IsNativeCarryRealOperatorZero
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  NativeCarryRealPlaneMassCompatible sigma time ∧
    NativeCarryRealOperatorBoundaryClosesAt camera sigma time

/--
Exact zero-set factorization for every camera width:

`Zero_camera = {1/2} × Resonance_camera`.

The proof uses only the quadratic mass rigidity of the uncompressed real
state.  The bracket is then transported by literal substitution of the unique
radial shell.
-/
theorem isNativeCarryRealOperatorZero_iff
    (camera : ℕ) (sigma time : ℝ) :
    IsNativeCarryRealOperatorZero camera sigma time ↔
      sigma = (1 : ℝ) / 2 ∧
        IsNativeCarryRealOperatorResonance camera time := by
  unfold IsNativeCarryRealOperatorZero
    IsNativeCarryRealOperatorResonance
  constructor
  · rintro ⟨hmass, hclose⟩
    have hsigma : sigma = (1 : ℝ) / 2 :=
      (nativeCarryRealPlaneMassCompatible_iff sigma time).1 hmass
    subst sigma
    exact ⟨rfl, hclose⟩
  · rintro ⟨hsigma, hresonance⟩
    subst sigma
    exact
      ⟨(nativeCarryRealPlaneMassCompatible_iff
          ((1 : ℝ) / 2) time).2 rfl,
        hresonance⟩

/--
Canonical confinement statement: a native operator zero has the unique radial
exponent selected by the carry mass.
-/
theorem nativeCarryRealOperatorZero_sigma_eq_half
    {camera : ℕ} {sigma time : ℝ}
    (hzero : IsNativeCarryRealOperatorZero camera sigma time) :
    sigma = (1 : ℝ) / 2 :=
  ((isNativeCarryRealOperatorZero_iff camera sigma time).1 hzero).1

/-- There are no native real-operator zeros on an off-critical radial shell. -/
theorem nativeCarryRealOperatorZero_ne_of_sigma_ne_half
    {camera : ℕ} {sigma time : ℝ}
    (hoff : sigma ≠ (1 : ℝ) / 2) :
    ¬ IsNativeCarryRealOperatorZero camera sigma time := by
  intro hzero
  exact hoff (nativeCarryRealOperatorZero_sigma_eq_half hzero)

/--
The earlier camera-three boundary predicate is definitionally the specialization
of the arbitrary-camera boundary used here.
-/
@[simp] theorem nativeCarryRealOperatorBoundaryClosesAt_three
    (sigma time : ℝ) :
    NativeCarryRealOperatorBoundaryClosesAt 3 sigma time ↔
      NativeCarryRealPlaneBoundaryClosesAt sigma time :=
  Iff.rfl

/--
The earlier admissible boundary closure is exactly the camera-three native
operator zero; no hypothesis has been added or removed.
-/
@[simp] theorem isNativeCarryRealOperatorZero_three_iff
    (sigma time : ℝ) :
    IsNativeCarryRealOperatorZero 3 sigma time ↔
      NativeCarryRealPlaneAdmissibleBoundaryClosesAt sigma time :=
  Iff.rfl

/--
Exact factorization of the previously named admissible camera-three closure.
This strengthens its one-way `sigma = 1/2` projection to an equivalence with
the complete native resonance predicate.
-/
theorem nativeCarryRealPlaneAdmissibleBoundaryClosesAt_iff_nativeResonance
    (sigma time : ℝ) :
    NativeCarryRealPlaneAdmissibleBoundaryClosesAt sigma time ↔
      sigma = (1 : ℝ) / 2 ∧
        IsNativeCarryRealOperatorResonance 3 time := by
  rw [← isNativeCarryRealOperatorZero_three_iff]
  exact isNativeCarryRealOperatorZero_iff 3 sigma time

end

end CPFormal.Analytic.Cp
