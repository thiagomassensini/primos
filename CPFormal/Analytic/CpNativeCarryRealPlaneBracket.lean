import CPFormal.Genuine.CpBracketPairing
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Native carry bracket in the real plane

This module formalizes the finite operator used by the primitive numerical
scanner without introducing a complex scalar field.

The state attached to a positive integer `n` is the real vector

`n^(-1/2) * (cos (-t log n), sin (-t log n))`.

The camera applies centered second differences coordinatewise and adds the
finite seed.  Its visible energy is the Euclidean quadratic energy of the
resultant.  The kernel proves:

* the state energy is exactly `n⁻¹`, independently of `t`;
* the finite camera is defined for every natural camera width, before any
  primality assumption;
* for an odd prime width it is exactly the already formalized finite Genuine
  chart, now instantiated in the real product ring;
* visible energy vanishes exactly when the real vector resultant vanishes.

Thus phase rotation, bracket synthesis, and zero detection are internally
defined over `R x R`.  A separate optional packaging module may compare this
real object with a complex notation, but that notation is not used here.
-/

open scoped BigOperators

namespace CPFormal.Analytic.Cp

noncomputable section

/-! ## Additive saturated camera before choosing a scalar field -/

/--
Seed plus saturated centered brackets.  Only an additive commutative group is
needed: the camera does not require multiplication or a complex scalar.
-/
def nativeCarryFiniteSaturatedChart
    {A : Type*} [AddCommGroup A]
    (p M : ℕ) (f : ℤ → A) : A :=
  (∑ n ∈ Finset.Icc (1 : ℤ)
      (CPFormal.Genuine.Cp.halfRange p : ℤ), f n) +
    ∑ k ∈ Finset.range M,
      CPFormal.saturatedBracket
        (CPFormal.Genuine.Cp.halfRange p) f
        (CPFormal.Genuine.Cp.alignedCenter p k)

/-- Additive maps commute exactly with the finite saturated camera. -/
theorem map_nativeCarryFiniteSaturatedChart
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (g : A →+ B) (p M : ℕ) (f : ℤ → A) :
    g (nativeCarryFiniteSaturatedChart p M f) =
      nativeCarryFiniteSaturatedChart p M (fun n => g (f n)) := by
  classical
  simp [nativeCarryFiniteSaturatedChart, CPFormal.saturatedBracket,
    CPFormal.centeredSecondDifference]

/--
For an odd prime camera, the additive saturated camera is literally the
existing finite Genuine chart.  Primality is used only for the identification
of the balanced-offset presentation with the symmetric radii presentation.
-/
theorem nativeCarryFiniteSaturatedChart_eq_finiteChart
    {R : Type*} [CommRing R]
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (f : ℤ → R) :
    nativeCarryFiniteSaturatedChart p M f =
      CPFormal.Genuine.Cp.finiteChart p M f := by
  classical
  unfold nativeCarryFiniteSaturatedChart
    CPFormal.Genuine.Cp.finiteChart
    CPFormal.Genuine.Cp.seedSum
  simp_rw [
    CPFormal.Genuine.Cp.bracket_eq_saturatedBracket
      p hp hpodd]

/-! ## Primitive real rotating state -/

/-- Real two-coordinate carrier used by the primitive scanner. -/
abbrev NativeCarryRealPlane := ℝ × ℝ

/-- Euclidean quadratic energy of a real carrier vector. -/
def nativeCarryRealPlaneEnergy (u : NativeCarryRealPlane) : ℝ :=
  u.1 ^ 2 + u.2 ^ 2

/-- Real unit direction at angle `theta`. -/
def nativeCarryRealDirection (theta : ℝ) : NativeCarryRealPlane :=
  (Real.cos theta, Real.sin theta)

/-- The real rotating direction has unit quadratic energy. -/
@[simp] theorem nativeCarryRealPlaneEnergy_direction (theta : ℝ) :
    nativeCarryRealPlaneEnergy (nativeCarryRealDirection theta) = 1 := by
  unfold nativeCarryRealPlaneEnergy nativeCarryRealDirection
  rw [add_comm, Real.sin_sq_add_cos_sq]

/--
Real-plane sample with an arbitrary radial amplitude exponent.  Camera indices
are positive; the nonpositive branch only makes the field total on `Z`.
-/
def nativeCarryRealPlaneSampleAt
    (sigma t : ℝ) (n : ℤ) : NativeCarryRealPlane :=
  if 0 < n then
    let amplitude := (n : ℝ) ^ (-sigma)
    let angle := -t * Real.log (n : ℝ)
    (amplitude * Real.cos angle, amplitude * Real.sin angle)
  else
    0

/-- Critical sample selected by the quadratic carry normalization. -/
def nativeCarryRealPlaneSample
    (t : ℝ) (n : ℤ) : NativeCarryRealPlane :=
  nativeCarryRealPlaneSampleAt ((1 : ℝ) / 2) t n

@[simp] theorem nativeCarryRealPlaneSampleAt_of_pos
    (sigma t : ℝ) {n : ℤ} (hn : 0 < n) :
    nativeCarryRealPlaneSampleAt sigma t n =
      let amplitude := (n : ℝ) ^ (-sigma)
      let angle := -t * Real.log (n : ℝ)
      (amplitude * Real.cos angle, amplitude * Real.sin angle) := by
  simp [nativeCarryRealPlaneSampleAt, hn]

@[simp] theorem nativeCarryRealPlaneSampleAt_of_nonpos
    (sigma t : ℝ) {n : ℤ} (hn : n ≤ 0) :
    nativeCarryRealPlaneSampleAt sigma t n = 0 := by
  simp [nativeCarryRealPlaneSampleAt, not_lt.mpr hn]

/--
The quadratic energy of a positive sample is the square of its radial
amplitude and is independent of the real rotation time.
-/
theorem nativeCarryRealPlaneEnergy_sampleAt
    (sigma t : ℝ) {n : ℤ} (hn : 0 < n) :
    nativeCarryRealPlaneEnergy
        (nativeCarryRealPlaneSampleAt sigma t n) =
      (n : ℝ) ^ (-2 * sigma) := by
  have hnR : 0 ≤ (n : ℝ) := by
    exact_mod_cast (le_of_lt hn)
  rw [nativeCarryRealPlaneSampleAt_of_pos sigma t hn]
  unfold nativeCarryRealPlaneEnergy
  dsimp only
  let angle : ℝ := -t * Real.log (n : ℝ)
  calc
    (((n : ℝ) ^ (-sigma)) * Real.cos angle) ^ 2 +
          (((n : ℝ) ^ (-sigma)) * Real.sin angle) ^ 2 =
        (((n : ℝ) ^ (-sigma)) ^ 2) *
          (Real.cos angle ^ 2 + Real.sin angle ^ 2) := by
      ring
    _ = (((n : ℝ) ^ (-sigma)) ^ 2) := by
      rw [add_comm, Real.sin_sq_add_cos_sq, mul_one]
    _ = (n : ℝ) ^ (-2 * sigma) := by
      rw [← Real.rpow_mul_natCast hnR (-sigma) 2]
      congr 1
      ring

/--
At the critical exponent, the sample energy is exactly the inverse integer
mass.
-/
theorem nativeCarryRealPlaneEnergy_sample
    (t : ℝ) {n : ℤ} (hn : 0 < n) :
    nativeCarryRealPlaneEnergy (nativeCarryRealPlaneSample t n) =
      ((n : ℝ))⁻¹ := by
  rw [nativeCarryRealPlaneSample,
    nativeCarryRealPlaneEnergy_sampleAt ((1 : ℝ) / 2) t hn]
  have hnR : 0 ≤ (n : ℝ) := by
    exact_mod_cast (le_of_lt hn)
  simpa using Real.rpow_neg hnR (1 : ℝ)

/--
An exponent belongs to the native real-vector domain when every positive
integer above the degenerate base `1` carries exactly the inverse quadratic
mass.
-/
def NativeCarryRealPlaneMassCompatible
    (sigma t : ℝ) : Prop :=
  ∀ n : ℤ, 1 < n →
    nativeCarryRealPlaneEnergy
        (nativeCarryRealPlaneSampleAt sigma t n) =
      ((n : ℝ))⁻¹

/--
The native real-vector domain has exactly one radial exponent.  The phase time
is arbitrary and does not participate in the rigidity.
-/
theorem nativeCarryRealPlaneMassCompatible_iff
    (sigma t : ℝ) :
    NativeCarryRealPlaneMassCompatible sigma t ↔
      sigma = (1 : ℝ) / 2 := by
  constructor
  · intro hcompatible
    have htwo := hcompatible 2 (by norm_num)
    rw [nativeCarryRealPlaneEnergy_sampleAt sigma t (by norm_num)] at htwo
    have hpow :
        (2 : ℝ) ^ (-2 * sigma) =
          (2 : ℝ) ^ (-1 : ℝ) := by
      simpa [Real.rpow_neg_one] using htwo
    have hexponent : -2 * sigma = (-1 : ℝ) :=
      (Real.rpow_right_inj (by norm_num) (by norm_num)).mp hpow
    linarith
  · intro hsigma
    subst sigma
    intro n hn
    exact nativeCarryRealPlaneEnergy_sample
      t (lt_trans (by norm_num) hn)

/-! ## Real finite camera and its zero predicate -/

/-- Finite real camera at an arbitrary radial exponent. -/
def nativeCarryRealPlaneFiniteChartAt
    (p M : ℕ) (sigma t : ℝ) : NativeCarryRealPlane :=
  nativeCarryFiniteSaturatedChart p M
    (nativeCarryRealPlaneSampleAt sigma t)

/-- Finite primitive camera, entirely valued in the real plane. -/
def nativeCarryRealPlaneFiniteChart
    (p M : ℕ) (t : ℝ) : NativeCarryRealPlane :=
  nativeCarryRealPlaneFiniteChartAt p M ((1 : ℝ) / 2) t

/--
For an odd prime width, the real primitive camera is the existing generic
Genuine chart instantiated in the real product ring.
-/
theorem nativeCarryRealPlaneFiniteChart_eq_finiteChart
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) (t : ℝ) :
    nativeCarryRealPlaneFiniteChart p M t =
      CPFormal.Genuine.Cp.finiteChart p M
        (nativeCarryRealPlaneSample t) := by
  unfold nativeCarryRealPlaneFiniteChart
    nativeCarryRealPlaneFiniteChartAt
    nativeCarryRealPlaneSample
  exact nativeCarryFiniteSaturatedChart_eq_finiteChart
    p M hp hpodd
      (nativeCarryRealPlaneSampleAt ((1 : ℝ) / 2) t)

/-- Euclidean energy is nonnegative. -/
theorem nativeCarryRealPlaneEnergy_nonneg
    (u : NativeCarryRealPlane) :
    0 ≤ nativeCarryRealPlaneEnergy u := by
  exact add_nonneg (sq_nonneg u.1) (sq_nonneg u.2)

/-- Euclidean energy detects the zero vector exactly. -/
theorem nativeCarryRealPlaneEnergy_eq_zero_iff
    (u : NativeCarryRealPlane) :
    nativeCarryRealPlaneEnergy u = 0 ↔ u = 0 := by
  rcases u with ⟨x, y⟩
  change x ^ 2 + y ^ 2 = 0 ↔ (x, y) = (0, 0)
  constructor
  · intro h
    have hx2 : x ^ 2 = 0 := by
      nlinarith [sq_nonneg y]
    have hy2 : y ^ 2 = 0 := by
      nlinarith [sq_nonneg x]
    have hx : x = 0 := by
      have hxmul : x * x = 0 := by simpa [pow_two] using hx2
      rcases mul_eq_zero.mp hxmul with hx | hx
      · exact hx
      · exact hx
    have hy : y = 0 := by
      have hymul : y * y = 0 := by simpa [pow_two] using hy2
      rcases mul_eq_zero.mp hymul with hy | hy
      · exact hy
      · exact hy
    rw [hx, hy]
  · intro h
    rw [h]
    norm_num

/--
The primitive scanner's raw visible energy vanishes exactly when its real
resultant vanishes.  No scalar outside the real plane is needed to state or
detect the zero.
-/
theorem nativeCarryRealPlaneFiniteChart_energy_eq_zero_iff
    (p M : ℕ) (t : ℝ) :
    nativeCarryRealPlaneEnergy
        (nativeCarryRealPlaneFiniteChart p M t) = 0 ↔
      nativeCarryRealPlaneFiniteChart p M t = 0 :=
  nativeCarryRealPlaneEnergy_eq_zero_iff _

/--
An admissible finite primitive zero keeps the vector state and the camera
resultant separate: mass compatibility is a domain condition, while zero is a
bracket observation.
-/
def NativeCarryRealPlaneAdmissibleFiniteZero
    (p M : ℕ) (sigma t : ℝ) : Prop :=
  NativeCarryRealPlaneMassCompatible sigma t ∧
    nativeCarryRealPlaneEnergy
      (nativeCarryRealPlaneFiniteChartAt p M sigma t) = 0

/--
Exact real-domain factorization: an admissible finite zero is the same as the
critical exponent together with a zero of the critical real camera.  The
bracket does not choose the exponent after the fact; the carry mass fixes the
domain before the camera is evaluated.
-/
theorem nativeCarryRealPlaneAdmissibleFiniteZero_iff
    (p M : ℕ) (sigma t : ℝ) :
    NativeCarryRealPlaneAdmissibleFiniteZero p M sigma t ↔
      sigma = (1 : ℝ) / 2 ∧
        nativeCarryRealPlaneEnergy
          (nativeCarryRealPlaneFiniteChart p M t) = 0 := by
  constructor
  · rintro ⟨hcompatible, hzero⟩
    have hsigma :=
      (nativeCarryRealPlaneMassCompatible_iff sigma t).1 hcompatible
    subst sigma
    exact ⟨rfl, hzero⟩
  · rintro ⟨hsigma, hzero⟩
    subst sigma
    exact ⟨
      (nativeCarryRealPlaneMassCompatible_iff ((1 : ℝ) / 2) t).2 rfl,
      hzero⟩

end

end CPFormal.Analytic.Cp
