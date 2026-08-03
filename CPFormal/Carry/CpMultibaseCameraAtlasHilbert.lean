import CPFormal.Carry.CpMultibaseCameraAtlas
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The multibase camera atlas as a direct sum of vertical lines

Realizing each prime camera as an independent coordinate axis of the free real
space `ℕ →₀ ℝ`, the quantity `n` becomes the vector `∑_q v_q(n) · e_q`
(`factorizationVector`).  The camera `p` resolves the axis `V_p = ℝ·e_p`
(`cameraVerticalLine`); everything it leaves horizontal lives in
`H_p = span {e_q : q ≠ p}` (`cameraHorizontalSpace`), which is exactly the span
of the *other* cameras' vertical axes.

The main structural theorem is that these are complementary,
`IsCompl (cameraVerticalLine p) (cameraHorizontalSpace p)`: the atlas is a clean
internal direct sum, so "horizontal in `p`" is precisely the closed sum of the
other verticals.  The linear functional `e_q ↦ log q` recovers the scalar log
decomposition of the companion module.
-/

open Finsupp

namespace CPFormal.Carry.Cp

/-- The camera-log space: the free real space with one axis per camera. -/
abbrev CameraLogSpace := ℕ →₀ ℝ

/-- The vertical axis (unit direction) of camera `q`. -/
noncomputable def cameraAxis (q : ℕ) : CameraLogSpace := Finsupp.single q 1

/-- The vertical line resolved by camera `p`: the axis `ℝ·e_p`. -/
def cameraVerticalLine (p : ℕ) : Submodule ℝ CameraLogSpace :=
  Finsupp.supported ℝ ℝ ({p} : Set ℕ)

/-- The horizontal subspace left by camera `p`: the span of the other axes. -/
def cameraHorizontalSpace (p : ℕ) : Submodule ℝ CameraLogSpace :=
  Finsupp.supported ℝ ℝ ({p}ᶜ : Set ℕ)

/-- The quantity `n` as the vector `∑_q v_q(n) · e_q`. -/
noncomputable def factorizationVector (n : ℕ) : CameraLogSpace :=
  Finsupp.mapRange (Nat.cast : ℕ → ℝ) Nat.cast_zero (n.factorization)

@[simp] theorem factorizationVector_apply (n q : ℕ) :
    factorizationVector n q = (n.factorization q : ℝ) := by
  rw [factorizationVector, Finsupp.mapRange_apply]

/-- The vertical line is the span of the `p`-axis. -/
theorem cameraVerticalLine_eq_span (p : ℕ) :
    cameraVerticalLine p = Submodule.span ℝ (cameraAxis '' ({p} : Set ℕ)) := by
  rw [cameraVerticalLine, Finsupp.supported_eq_span_single]
  simp only [cameraAxis]

/-- The horizontal subspace is the span of the *other* cameras' axes. -/
theorem cameraHorizontalSpace_eq_span (p : ℕ) :
    cameraHorizontalSpace p = Submodule.span ℝ (cameraAxis '' ({p}ᶜ : Set ℕ)) := by
  rw [cameraHorizontalSpace, Finsupp.supported_eq_span_single]
  simp only [cameraAxis]

/-- Atlas completeness: vertical `p` plus horizontal `p` is the whole space. -/
theorem cameraVertical_sup_horizontal (p : ℕ) :
    cameraVerticalLine p ⊔ cameraHorizontalSpace p = ⊤ := by
  rw [cameraVerticalLine, cameraHorizontalSpace, ← Finsupp.supported_union,
    Set.union_compl_self]
  exact Finsupp.supported_univ

/-- Atlas independence: vertical `p` and horizontal `p` are disjoint. -/
theorem cameraVertical_disjoint_horizontal (p : ℕ) :
    Disjoint (cameraVerticalLine p) (cameraHorizontalSpace p) := by
  rw [cameraVerticalLine, cameraHorizontalSpace,
    Finsupp.disjoint_supported_supported_iff]
  exact disjoint_compl_right

/-- The camera atlas is a clean internal direct sum: the horizontal subspace of
`p` is precisely the complement of the vertical line of `p`, i.e. the (closed)
sum of the other cameras' verticals. -/
theorem isCompl_cameraVertical_horizontal (p : ℕ) :
    IsCompl (cameraVerticalLine p) (cameraHorizontalSpace p) :=
  ⟨cameraVertical_disjoint_horizontal p,
    codisjoint_iff.mpr (cameraVertical_sup_horizontal p)⟩

/-- The horizontal part of `n`'s vector (after removing camera `p`'s vertical
voice) lives in the horizontal subspace: what `p` leaves is the other cameras'. -/
theorem factorizationVector_horizontal_mem (n p : ℕ) :
    factorizationVector n - (n.factorization p : ℝ) • cameraAxis p ∈
      cameraHorizontalSpace p := by
  rw [cameraHorizontalSpace, Finsupp.mem_supported]
  have hp0 : (factorizationVector n - (n.factorization p : ℝ) • cameraAxis p) p = 0 := by
    simp [Finsupp.sub_apply, cameraAxis, Finsupp.single_eq_same]
  intro q hq
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  rintro rfl
  rw [Finset.mem_coe, Finsupp.mem_support_iff] at hq
  exact hq hp0

/-- The log functional `e_q ↦ log q` on the camera-log space. -/
noncomputable def logEval : CameraLogSpace →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (fun q : ℕ => Real.log q)

@[simp] theorem logEval_cameraAxis (q : ℕ) : logEval (cameraAxis q) = Real.log q := by
  simp [logEval, cameraAxis]

/-- The log functional recovers `log n` from the quantity's vector: the vector
picture and the scalar log decomposition agree. -/
theorem logEval_factorizationVector {n : ℕ} (hn : n ≠ 0) :
    logEval (factorizationVector n) = Real.log n := by
  have hsupp : (factorizationVector n).support = n.factorization.support := by
    ext q
    rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff, factorizationVector_apply,
      Nat.cast_ne_zero]
  rw [logEval, Finsupp.linearCombination_apply, Finsupp.sum, hsupp,
    log_eq_sum_vertical hn]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [factorizationVector_apply, smul_eq_mul]

end CPFormal.Carry.Cp
