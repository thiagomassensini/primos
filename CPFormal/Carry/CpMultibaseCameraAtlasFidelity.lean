import CPFormal.Carry.CpMultibaseCameraAtlasHilbert

/-!
# Fidelity firewall for the scalar log observer

The atlas stores each camera's coordinate without overlap (an internal direct
sum).  A single scalar observer, however, is *not* faithful on the whole free
space: this module isolates the exact boundary.

* On the positive arithmetic cone — nonnegative coordinates supported on cameras
  `q ≥ 2` — the log observer `logEval` is faithful
  (`logEval_faithful_on_positiveCone`): a zero reading forces the vector to
  vanish, because every voice `log q > 0` and every weight is nonnegative.

* Off that cone there is an explicit blind direction
  (`blindVector = log 3 · e₂ − log 2 · e₃`): it is nonzero yet reads exactly
  zero (`logEval_blindVector`, `blindVector_ne_zero`).

This firewall forbids reading "the atlas is a direct sum" as "a single readout
observes every coordinate".  The first is true; the second is false in general.
-/

open Finsupp

namespace CPFormal.Carry.Cp

/-- On the positive arithmetic cone (nonnegative coordinates supported on
cameras `q ≥ 2`), the scalar log observer is faithful. -/
theorem logEval_faithful_on_positiveCone {x : CameraLogSpace}
    (hpos : ∀ q, 0 ≤ x q) (hsupp : ∀ q ∈ x.support, 2 ≤ q)
    (h0 : logEval x = 0) : x = 0 := by
  rw [logEval, Finsupp.linearCombination_apply, Finsupp.sum] at h0
  simp only [smul_eq_mul] at h0
  have hnn : ∀ q ∈ x.support, 0 ≤ x q * Real.log q := by
    intro q hq
    have h1q : (1 : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast le_trans (by norm_num : (1 : ℕ) ≤ 2) (hsupp q hq)
    exact mul_nonneg (hpos q) (Real.log_nonneg h1q)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0
  ext q
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  by_cases hq : q ∈ x.support
  · have hlogq : (0 : ℝ) < Real.log q :=
      Real.log_pos (by exact_mod_cast (hsupp q hq))
    rcases mul_eq_zero.mp (hzero q hq) with h | h
    · exact h
    · exact absurd h (ne_of_gt hlogq)
  · by_contra hne
    exact hq (Finsupp.mem_support_iff.mpr hne)

/-- An explicit blind direction of the scalar observer, off the positive cone. -/
noncomputable def blindVector : CameraLogSpace :=
  Real.log 3 • cameraAxis 2 - Real.log 2 • cameraAxis 3

/-- The blind direction reads exactly zero. -/
theorem logEval_blindVector : logEval blindVector = 0 := by
  simp only [blindVector, map_sub, map_smul, logEval_cameraAxis, smul_eq_mul,
    Nat.cast_ofNat]
  ring

/-- The blind direction is nonzero. -/
theorem blindVector_ne_zero : blindVector ≠ 0 := by
  intro h
  have h2 : blindVector 2 = Real.log 3 := by
    simp [blindVector, cameraAxis, Finsupp.sub_apply]
  rw [h] at h2
  simp only [Finsupp.coe_zero, Pi.zero_apply] at h2
  exact absurd h2.symm (ne_of_gt (Real.log_pos (by norm_num)))

/-- The firewall in one statement: `logEval` has a nonzero kernel vector, so a
single scalar reading cannot certify that the underlying atlas vector vanishes. -/
theorem exists_nonzero_logEval_kernel :
    ∃ x : CameraLogSpace, x ≠ 0 ∧ logEval x = 0 :=
  ⟨blindVector, blindVector_ne_zero, logEval_blindVector⟩

end CPFormal.Carry.Cp
