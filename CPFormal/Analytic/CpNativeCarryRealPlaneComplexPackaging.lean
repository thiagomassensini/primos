import CPFormal.Analytic.CpNativeCarryRealPlaneBracket
import Mathlib.Data.Complex.Basic

/-!
# Optional complex packaging of the native real-plane camera

The primitive camera, its quadratic energy, and its zero predicate were defined
in `CpNativeCarryRealPlaneBracket` using only real pairs and additive centered
differences.

This module proves that storing a real pair `(x,y)` in the two fields of a
complex number is an injective additive encoding.  The encoding commutes with
every finite saturated camera, preserves quadratic energy through `normSq`, and
therefore preserves zeros exactly.

No imaginary-unit multiplication or complex exponential is used.  The complex
value is only a two-coordinate container for an operator already defined over
the real plane.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Store a real-plane vector in the real and imaginary coordinate fields. -/
def nativeCarryRealPlaneComplexPackaging :
    NativeCarryRealPlane →+ ℂ where
  toFun u := ⟨u.1, u.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem nativeCarryRealPlaneComplexPackaging_re
    (u : NativeCarryRealPlane) :
    (nativeCarryRealPlaneComplexPackaging u).re = u.1 := rfl

@[simp] theorem nativeCarryRealPlaneComplexPackaging_im
    (u : NativeCarryRealPlane) :
    (nativeCarryRealPlaneComplexPackaging u).im = u.2 := rfl

/-- The coordinate packaging is injective. -/
theorem nativeCarryRealPlaneComplexPackaging_injective :
    Function.Injective nativeCarryRealPlaneComplexPackaging := by
  intro u v huv
  apply Prod.ext
  · exact congrArg Complex.re huv
  · exact congrArg Complex.im huv

/-- Complex squared norm is exactly the previously defined real energy. -/
@[simp] theorem normSq_nativeCarryRealPlaneComplexPackaging
    (u : NativeCarryRealPlane) :
    Complex.normSq (nativeCarryRealPlaneComplexPackaging u) =
      nativeCarryRealPlaneEnergy u := by
  simp [Complex.normSq, nativeCarryRealPlaneComplexPackaging,
    nativeCarryRealPlaneEnergy, pow_two]

/--
Packaging commutes with the whole finite real camera.  This is a direct
instance of the additive naturality theorem; no analytic identity is involved.
-/
theorem nativeCarryRealPlaneComplexPackaging_finiteChartAt
    (p M : ℕ) (sigma t : ℝ) :
    nativeCarryRealPlaneComplexPackaging
        (nativeCarryRealPlaneFiniteChartAt p M sigma t) =
      nativeCarryFiniteSaturatedChart p M
        (fun n =>
          nativeCarryRealPlaneComplexPackaging
            (nativeCarryRealPlaneSampleAt sigma t n)) := by
  exact map_nativeCarryFiniteSaturatedChart
    nativeCarryRealPlaneComplexPackaging p M
    (nativeCarryRealPlaneSampleAt sigma t)

/--
For every camera width, prime or composite, packaging preserves the zero
predicate of an arbitrary real-plane input field.
-/
theorem nativeCarryFiniteSaturatedChart_zero_iff_packaged_zero
    (p M : ℕ) (f : ℤ → NativeCarryRealPlane) :
    nativeCarryFiniteSaturatedChart p M f = 0 ↔
      nativeCarryFiniteSaturatedChart p M
        (fun n => nativeCarryRealPlaneComplexPackaging (f n)) = 0 := by
  constructor
  · intro hreal
    have hpack :=
      map_nativeCarryFiniteSaturatedChart
        nativeCarryRealPlaneComplexPackaging p M f
    rw [hreal] at hpack
    simpa using hpack.symm
  · intro hpackaged
    apply nativeCarryRealPlaneComplexPackaging_injective
    rw [map_zero]
    calc
      nativeCarryRealPlaneComplexPackaging
          (nativeCarryFiniteSaturatedChart p M f) =
          nativeCarryFiniteSaturatedChart p M
            (fun n => nativeCarryRealPlaneComplexPackaging (f n)) :=
        map_nativeCarryFiniteSaturatedChart
          nativeCarryRealPlaneComplexPackaging p M f
      _ = 0 := hpackaged

/--
For every camera width, packaging also preserves the quadratic energy of the
resultant.
-/
theorem normSq_packaged_nativeCarryFiniteSaturatedChart
    (p M : ℕ) (f : ℤ → NativeCarryRealPlane) :
    Complex.normSq
        (nativeCarryFiniteSaturatedChart p M
          (fun n => nativeCarryRealPlaneComplexPackaging (f n))) =
      nativeCarryRealPlaneEnergy
        (nativeCarryFiniteSaturatedChart p M f) := by
  rw [← map_nativeCarryFiniteSaturatedChart
    nativeCarryRealPlaneComplexPackaging p M f]
  exact normSq_nativeCarryRealPlaneComplexPackaging _

/--
For an odd prime camera, the packaged real resultant is literally the generic
finite Genuine chart evaluated on the packaged real samples.
-/
theorem nativeCarryRealPlaneComplexPackaging_eq_finiteChart
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (sigma t : ℝ) :
    nativeCarryRealPlaneComplexPackaging
        (nativeCarryRealPlaneFiniteChartAt p M sigma t) =
      CPFormal.Genuine.Cp.finiteChart p M
        (fun n =>
          nativeCarryRealPlaneComplexPackaging
            (nativeCarryRealPlaneSampleAt sigma t n)) := by
  calc
    nativeCarryRealPlaneComplexPackaging
          (nativeCarryRealPlaneFiniteChartAt p M sigma t) =
        nativeCarryFiniteSaturatedChart p M
          (fun n =>
            nativeCarryRealPlaneComplexPackaging
              (nativeCarryRealPlaneSampleAt sigma t n)) :=
      nativeCarryRealPlaneComplexPackaging_finiteChartAt
        p M sigma t
    _ = CPFormal.Genuine.Cp.finiteChart p M
          (fun n =>
            nativeCarryRealPlaneComplexPackaging
              (nativeCarryRealPlaneSampleAt sigma t n)) :=
      nativeCarryFiniteSaturatedChart_eq_finiteChart
        p M hp hpodd _

/--
The real camera and its packaged finite Genuine chart have exactly the same
zero predicate.
-/
theorem nativeCarryRealPlaneFiniteChartAt_zero_iff_packaged_zero
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (sigma t : ℝ) :
    nativeCarryRealPlaneFiniteChartAt p M sigma t = 0 ↔
      CPFormal.Genuine.Cp.finiteChart p M
        (fun n =>
          nativeCarryRealPlaneComplexPackaging
            (nativeCarryRealPlaneSampleAt sigma t n)) = 0 := by
  constructor
  · intro hreal
    have hpack :=
      nativeCarryRealPlaneComplexPackaging_eq_finiteChart
        p M hp hpodd sigma t
    rw [hreal] at hpack
    simpa using hpack.symm
  · intro hpackaged
    apply nativeCarryRealPlaneComplexPackaging_injective
    rw [map_zero]
    calc
      nativeCarryRealPlaneComplexPackaging
          (nativeCarryRealPlaneFiniteChartAt p M sigma t) =
          CPFormal.Genuine.Cp.finiteChart p M
            (fun n =>
              nativeCarryRealPlaneComplexPackaging
                (nativeCarryRealPlaneSampleAt sigma t n)) :=
        nativeCarryRealPlaneComplexPackaging_eq_finiteChart
          p M hp hpodd sigma t
      _ = 0 := hpackaged

/--
Packaging preserves the visible energy of the whole camera resultant.
-/
theorem normSq_packaged_finiteChart_eq_realEnergy
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (sigma t : ℝ) :
    Complex.normSq
        (CPFormal.Genuine.Cp.finiteChart p M
          (fun n =>
            nativeCarryRealPlaneComplexPackaging
              (nativeCarryRealPlaneSampleAt sigma t n))) =
      nativeCarryRealPlaneEnergy
        (nativeCarryRealPlaneFiniteChartAt p M sigma t) := by
  rw [← nativeCarryRealPlaneComplexPackaging_eq_finiteChart
    p M hp hpodd sigma t]
  exact normSq_nativeCarryRealPlaneComplexPackaging _

end

end CPFormal.Analytic.Cp
