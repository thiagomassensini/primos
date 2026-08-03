import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Multibase camera atlas: horizontal-in-p is the other cameras' verticals

For a positive integer `n` and a prime camera `p`, the unique factorization gives

`n = p ^ (v_p n) * cameraHorizontal n p`,   `cameraHorizontal n p = ∏_{q ≠ p} q ^ (v_q n)`,

so what camera `p` resolves *vertically* is `p ^ (v_p n)`, while what it leaves
*horizontal* is exactly the product of the *other* cameras' vertical
resolutions.  In logarithms this is the "chord of voices":

`log n = (v_p n) · log p + ∑_{q ≠ p} (v_q n) · log q`.

Here `v_q n = n.factorization q` is the `q`-adic depth.
-/

open Finset

namespace CPFormal.Carry.Cp

/-- Vertical resolution of camera `p` at `n`: the `p`-adic depth `v_p(n)`. -/
abbrev cameraVertical (n p : ℕ) : ℕ := n.factorization p

/-- Horizontal remainder of camera `p` at `n`: the product of the other
cameras' vertical resolutions, `∏_{q ≠ p} q ^ (v_q n)`. -/
def cameraHorizontal (n p : ℕ) : ℕ :=
  ∏ q ∈ (n.factorization.support).erase p, q ^ (n.factorization q)

/-- The horizontal remainder is never zero. -/
theorem cameraHorizontal_ne_zero (n p : ℕ) : cameraHorizontal n p ≠ 0 := by
  rw [cameraHorizontal]
  refine Finset.prod_ne_zero_iff.mpr (fun q hq => ?_)
  rw [Finset.mem_erase, Nat.support_factorization] at hq
  exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hq.2).pos.ne'

/-- Exact vertical/horizontal split of the quantity: what camera `p` resolves
vertically times what it leaves horizontal is the original quantity. -/
theorem multibase_vertical_horizontal_split {n : ℕ} (hn : n ≠ 0) (p : ℕ) :
    p ^ cameraVertical n p * cameraHorizontal n p = n := by
  classical
  have hprod : ∏ q ∈ n.factorization.support, q ^ (n.factorization q) = n := by
    have h := Nat.prod_factorization_pow_eq_self hn
    rwa [Finsupp.prod] at h
  by_cases hp : p ∈ n.factorization.support
  · rw [cameraVertical, cameraHorizontal,
      Finset.mul_prod_erase _ (fun q => q ^ (n.factorization q)) hp, hprod]
  · have hpf : n.factorization p = 0 := by
      by_contra hne
      exact hp (Finsupp.mem_support_iff.mpr hne)
    rw [cameraVertical, cameraHorizontal, hpf, pow_zero, one_mul,
      Finset.erase_eq_of_notMem hp, hprod]

/-- Full log decomposition of the quantity over all camera voices. -/
theorem log_eq_sum_vertical {n : ℕ} (hn : n ≠ 0) :
    Real.log n = ∑ q ∈ n.factorization.support, (n.factorization q : ℝ) * Real.log q := by
  have hcast : (n : ℝ) = ∏ q ∈ n.factorization.support, (q : ℝ) ^ (n.factorization q) := by
    have h := Nat.prod_factorization_pow_eq_self hn
    rw [Finsupp.prod] at h
    calc (n : ℝ)
        = ((∏ q ∈ n.factorization.support, q ^ (n.factorization q) : ℕ) : ℝ) := by rw [h]
      _ = ∏ q ∈ n.factorization.support, (q : ℝ) ^ (n.factorization q) := by push_cast; ring
  rw [hcast, Real.log_prod]
  · exact Finset.sum_congr rfl (fun q _ => Real.log_pow _ _)
  · intro q hq
    rw [Nat.support_factorization] at hq
    exact pow_ne_zero _ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos.ne')

/-- The horizontal log is exactly the sum of the other cameras' vertical voices. -/
theorem log_cameraHorizontal_eq_sum_erase (n p : ℕ) :
    Real.log (cameraHorizontal n p) =
      ∑ q ∈ (n.factorization.support).erase p, (n.factorization q : ℝ) * Real.log q := by
  rw [cameraHorizontal]
  push_cast
  rw [Real.log_prod]
  · exact Finset.sum_congr rfl (fun q _ => Real.log_pow _ _)
  · intro q hq
    rw [Finset.mem_erase, Nat.support_factorization] at hq
    exact pow_ne_zero _ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq.2).pos.ne')

/-- Camera `p` splits the log quantity into its own vertical voice plus the
horizontal log. -/
theorem log_camera_split {n : ℕ} (hn : n ≠ 0) {p : ℕ} (hp : p.Prime) :
    Real.log n =
      (cameraVertical n p : ℝ) * Real.log p + Real.log (cameraHorizontal n p) := by
  have hcH : cameraHorizontal n p ≠ 0 := cameraHorizontal_ne_zero n p
  have hsplit : ((p ^ cameraVertical n p * cameraHorizontal n p : ℕ) : ℝ) = (n : ℝ) := by
    exact_mod_cast multibase_vertical_horizontal_split hn p
  rw [← hsplit]
  push_cast
  rw [Real.log_mul (pow_ne_zero _ (by exact_mod_cast hp.pos.ne'))
      (by exact_mod_cast hcH), Real.log_pow]

/-- The camera-voice identity (Section 4): the total log is the voice opened by
camera `p` plus the pooled voices of all the other cameras. -/
theorem log_camera_voice {n : ℕ} (hn : n ≠ 0) {p : ℕ} (hp : p.Prime) :
    Real.log n =
      (n.factorization p : ℝ) * Real.log p +
        ∑ q ∈ (n.factorization.support).erase p,
          (n.factorization q : ℝ) * Real.log q := by
  rw [log_camera_split hn hp, log_cameraHorizontal_eq_sum_erase n p]

end CPFormal.Carry.Cp
