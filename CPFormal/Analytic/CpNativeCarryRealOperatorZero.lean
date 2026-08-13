import CPFormal.Analytic.CpNativeCarryRealPlaneGreenRigidity
import CPFormal.Analytic.CpNativeCarryRealSpectralBoundaryCarrier

/-!
# Native real-operator zeros

The quadratic carry law and the zero predicate are deliberately kept
separate in this module.

* `NativeCarryRealPlaneMassCompatible sigma time` records the quadratic
  equilibrium selected by positional carry and is equivalent to
  `sigma = 1 / 2`.
* `IsNativeCarryRealOperatorZero camera sigma time` records only that the
  finite real camera tends to zero.

Consequently, a zero away from the equilibrium shell is still a zero.  The
off-equilibrium displacement is detected separately by the Green center (or
by the completed two-channel Green operator); it is not built into the
meaning of zero.

No primality assumption and no complex coordinate are used here.
-/

open scoped Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/--
Boundary closure of an arbitrary real saturated camera at radial coordinate
`sigma` and real phase time `time`.
-/
def NativeCarryRealOperatorBoundaryClosesAt
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  Tendsto
    (fun cutoff : ℕ =>
      nativeCarryRealPlaneFiniteChartAt camera cutoff sigma time)
    atTop (nhds 0)

/--
A native real-operator zero is exactly boundary closure.  Quadratic mass
compatibility is a distinct, prior property and is not conjoined here.
-/
def IsNativeCarryRealOperatorZero
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  NativeCarryRealOperatorBoundaryClosesAt camera sigma time

/-- A resonance is the specialization of the zero predicate to equilibrium. -/
def IsNativeCarryRealOperatorResonance
    (camera : ℕ) (time : ℝ) : Prop :=
  IsNativeCarryRealOperatorZero camera ((1 : ℝ) / 2) time

/-- The public zero predicate introduces no condition beyond vanishing. -/
@[simp] theorem isNativeCarryRealOperatorZero_iff
    (camera : ℕ) (sigma time : ℝ) :
    IsNativeCarryRealOperatorZero camera sigma time ↔
      NativeCarryRealOperatorBoundaryClosesAt camera sigma time :=
  Iff.rfl

/-- At `sigma = 1 / 2`, a zero is definitionally a native resonance. -/
@[simp] theorem isNativeCarryRealOperatorZero_half_iff_resonance
    (camera : ℕ) (time : ℝ) :
    IsNativeCarryRealOperatorZero camera ((1 : ℝ) / 2) time ↔
      IsNativeCarryRealOperatorResonance camera time :=
  Iff.rfl

/--
The earlier camera-three boundary predicate is definitionally the
specialization of the arbitrary-camera boundary used here.
-/
@[simp] theorem nativeCarryRealOperatorBoundaryClosesAt_three
    (sigma time : ℝ) :
    NativeCarryRealOperatorBoundaryClosesAt 3 sigma time ↔
      NativeCarryRealPlaneBoundaryClosesAt sigma time :=
  Iff.rfl

/-- Camera-three zeros are exactly camera-three boundary closure. -/
@[simp] theorem isNativeCarryRealOperatorZero_three_iff
    (sigma time : ℝ) :
    IsNativeCarryRealOperatorZero 3 sigma time ↔
      NativeCarryRealPlaneBoundaryClosesAt sigma time :=
  Iff.rfl

/--
Mass-balanced closure is the intersection of two separate facts: quadratic
equilibrium and zero. It is not itself the definition of a zero.
-/
theorem nativeCarryRealPlaneMassBalancedBoundaryClosesAt_iff
    (sigma time : ℝ) :
    NativeCarryRealPlaneMassBalancedBoundaryClosesAt sigma time ↔
      NativeCarryRealPlaneMassCompatible sigma time ∧
        IsNativeCarryRealOperatorZero 3 sigma time :=
  Iff.rfl

end

end CPFormal.Analytic.Cp
