import CPFormal.Analytic.CpGenuineTiltPhaseCancellation

/-!
# Quantitative domination for the canonical Genuine tilt

This module develops sharp scalar second-difference bounds without taking a
norm before the two symmetric legs are combined.  The key input is a bound on

`f'' (center - t) + f'' (center + t)`.

Two applications of the one-dimensional fencing theorem then retain the exact
quadratic constant.  This is the quantitative tool needed to compare the
phase-bearing canonical tilt blocks before testing whether their tail can
cancel the first block.
-/

open scoped BigOperators

namespace CPFormal.Analytic.Cp

noncomputable section

/-- A symmetric lower bound for the second derivative gives the corresponding
sharp lower bound for the centered second difference. -/
theorem centeredSecondDifference_ge_of_pair_secondDeriv_ge
    {f f' f'' : ℝ → ℝ} {center radius C : ℝ}
    (hradius : 0 ≤ radius)
    (hfminus : ∀ t ∈ Set.Icc (0 : ℝ) radius,
      HasDerivAt f (f' (center - t)) (center - t))
    (hfplus : ∀ t ∈ Set.Icc (0 : ℝ) radius,
      HasDerivAt f (f' (center + t)) (center + t))
    (hf'minus : ∀ t ∈ Set.Icc (0 : ℝ) radius,
      HasDerivAt f' (f'' (center - t)) (center - t))
    (hf'plus : ∀ t ∈ Set.Icc (0 : ℝ) radius,
      HasDerivAt f' (f'' (center + t)) (center + t))
    (hpair : ∀ t ∈ Set.Icc (0 : ℝ) radius,
      2 * C ≤ f'' (center - t) + f'' (center + t)) :
    C * radius ^ 2 ≤
      f (center - radius) - 2 * f center + f (center + radius) := by
  let d : ℝ → ℝ := fun t ↦ f' (center + t) - f' (center - t)
  let q : ℝ → ℝ := fun t ↦ C * (2 * t)
  have hd : ∀ t ∈ Set.Icc (0 : ℝ) radius,
      HasDerivAt d (f'' (center + t) + f'' (center - t)) t := by
    intro t ht
    have hinnerMinus :
        HasDerivAt (fun u : ℝ ↦ center - u) (-1 : ℝ) t := by
      exact (hasDerivAt_id' t).const_sub center
    have hinnerPlus :
        HasDerivAt (fun u : ℝ ↦ center + u) (1 : ℝ) t := by
      exact (hasDerivAt_id' t).const_add center
    have hminus :
        HasDerivAt (fun u : ℝ ↦ f' (center - u))
          (-f'' (center - t)) t := by
      simpa [Function.comp_def] using
        (hf'minus t ht).scomp t hinnerMinus
    have hplus :
        HasDerivAt (fun u : ℝ ↦ f' (center + u))
          (f'' (center + t)) t := by
      simpa [Function.comp_def] using
        (hf'plus t ht).scomp t hinnerPlus
    have hsum := hplus.fun_add hminus.neg
    simpa [d, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum
  have hq : ∀ t : ℝ, HasDerivAt q (C * 2) t := by
    intro t
    have htwo : HasDerivAt (fun u : ℝ ↦ 2 * u) 2 t := by
      simpa using (hasDerivAt_id t).const_mul 2
    simpa [q] using htwo.const_mul C
  have hqd : ∀ t ∈ Set.Icc (0 : ℝ) radius, q t ≤ d t := by
    apply image_le_of_deriv_right_le_deriv_boundary
      (f := q) (f' := fun _ ↦ C * 2)
      (B := d) (B' := fun t ↦ f'' (center + t) + f'' (center - t))
    · intro t ht
      exact (hq t).continuousAt.continuousWithinAt
    · intro t ht
      exact (hq t).hasDerivWithinAt
    · simp [q, d]
    · intro t ht
      exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hd t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt
    · intro t ht
      simpa [mul_comm, add_comm] using hpair t (Set.Ico_subset_Icc_self ht)
  let g : ℝ → ℝ := fun t ↦
    f (center - t) + f (center + t) - 2 * f center
  let a : ℝ → ℝ := fun t ↦ C * t ^ 2
  have hg : ∀ t ∈ Set.Icc (0 : ℝ) radius, HasDerivAt g (d t) t := by
    intro t ht
    have hinnerMinus :
        HasDerivAt (fun u : ℝ ↦ center - u) (-1 : ℝ) t := by
      exact (hasDerivAt_id' t).const_sub center
    have hinnerPlus :
        HasDerivAt (fun u : ℝ ↦ center + u) (1 : ℝ) t := by
      exact (hasDerivAt_id' t).const_add center
    have hminus :
        HasDerivAt (fun u : ℝ ↦ f (center - u))
          (-f' (center - t)) t := by
      simpa [Function.comp_def] using
        (hfminus t ht).scomp t hinnerMinus
    have hplus :
        HasDerivAt (fun u : ℝ ↦ f (center + u))
          (f' (center + t)) t := by
      simpa [Function.comp_def] using
        (hfplus t ht).scomp t hinnerPlus
    have hsum := hminus.fun_add hplus
    have hconst := hsum.sub_const (2 * f center)
    simpa [g, d, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hconst
  have ha : ∀ t : ℝ, HasDerivAt a (q t) t := by
    intro t
    simpa [a, q] using ((hasDerivAt_id t).pow 2).const_mul C
  have hag : ∀ t ∈ Set.Icc (0 : ℝ) radius, a t ≤ g t := by
    apply image_le_of_deriv_right_le_deriv_boundary
      (f := a) (f' := q) (B := g) (B' := d)
    · intro t ht
      exact (ha t).continuousAt.continuousWithinAt
    · intro t ht
      exact (ha t).hasDerivWithinAt
    · dsimp [a, g]
      nlinarith
    · intro t ht
      exact (hg t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hg t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt
    · intro t ht
      exact hqd t (Set.Ico_subset_Icc_self ht)
  have hfinal := hag radius ⟨hradius, le_rfl⟩
  dsimp [a, g] at hfinal
  convert hfinal using 1 <;> ring

/-- A symmetric upper bound for the second derivative gives the corresponding
sharp upper bound for the centered second difference. -/
theorem centeredSecondDifference_le_of_pair_secondDeriv_le
    {f f' f'' : ℝ → ℝ} {center radius C : ℝ}
    (hradius : 0 ≤ radius)
    (hfminus : ∀ t ∈ Set.Icc (0 : ℝ) radius,
      HasDerivAt f (f' (center - t)) (center - t))
    (hfplus : ∀ t ∈ Set.Icc (0 : ℝ) radius,
      HasDerivAt f (f' (center + t)) (center + t))
    (hf'minus : ∀ t ∈ Set.Icc (0 : ℝ) radius,
      HasDerivAt f' (f'' (center - t)) (center - t))
    (hf'plus : ∀ t ∈ Set.Icc (0 : ℝ) radius,
      HasDerivAt f' (f'' (center + t)) (center + t))
    (hpair : ∀ t ∈ Set.Icc (0 : ℝ) radius,
      f'' (center - t) + f'' (center + t) ≤ 2 * C) :
    f (center - radius) - 2 * f center + f (center + radius) ≤
      C * radius ^ 2 := by
  let d : ℝ → ℝ := fun t ↦ f' (center + t) - f' (center - t)
  let q : ℝ → ℝ := fun t ↦ C * (2 * t)
  have hd : ∀ t ∈ Set.Icc (0 : ℝ) radius,
      HasDerivAt d (f'' (center + t) + f'' (center - t)) t := by
    intro t ht
    have hinnerMinus :
        HasDerivAt (fun u : ℝ ↦ center - u) (-1 : ℝ) t := by
      exact (hasDerivAt_id' t).const_sub center
    have hinnerPlus :
        HasDerivAt (fun u : ℝ ↦ center + u) (1 : ℝ) t := by
      exact (hasDerivAt_id' t).const_add center
    have hminus :
        HasDerivAt (fun u : ℝ ↦ f' (center - u))
          (-f'' (center - t)) t := by
      simpa [Function.comp_def] using
        (hf'minus t ht).scomp t hinnerMinus
    have hplus :
        HasDerivAt (fun u : ℝ ↦ f' (center + u))
          (f'' (center + t)) t := by
      simpa [Function.comp_def] using
        (hf'plus t ht).scomp t hinnerPlus
    have hsum := hplus.fun_add hminus.neg
    simpa [d, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum
  have hq : ∀ t : ℝ, HasDerivAt q (C * 2) t := by
    intro t
    have htwo : HasDerivAt (fun u : ℝ ↦ 2 * u) 2 t := by
      simpa using (hasDerivAt_id t).const_mul 2
    simpa [q] using htwo.const_mul C
  have hdq : ∀ t ∈ Set.Icc (0 : ℝ) radius, d t ≤ q t := by
    apply image_le_of_deriv_right_le_deriv_boundary
      (f := d) (f' := fun t ↦ f'' (center + t) + f'' (center - t))
      (B := q) (B' := fun _ ↦ C * 2)
    · intro t ht
      exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hd t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt
    · simp [q, d]
    · intro t ht
      exact (hq t).continuousAt.continuousWithinAt
    · intro t ht
      exact (hq t).hasDerivWithinAt
    · intro t ht
      simpa [mul_comm, add_comm] using hpair t (Set.Ico_subset_Icc_self ht)
  let g : ℝ → ℝ := fun t ↦
    f (center - t) + f (center + t) - 2 * f center
  let a : ℝ → ℝ := fun t ↦ C * t ^ 2
  have hg : ∀ t ∈ Set.Icc (0 : ℝ) radius, HasDerivAt g (d t) t := by
    intro t ht
    have hinnerMinus :
        HasDerivAt (fun u : ℝ ↦ center - u) (-1 : ℝ) t := by
      exact (hasDerivAt_id' t).const_sub center
    have hinnerPlus :
        HasDerivAt (fun u : ℝ ↦ center + u) (1 : ℝ) t := by
      exact (hasDerivAt_id' t).const_add center
    have hminus :
        HasDerivAt (fun u : ℝ ↦ f (center - u))
          (-f' (center - t)) t := by
      simpa [Function.comp_def] using
        (hfminus t ht).scomp t hinnerMinus
    have hplus :
        HasDerivAt (fun u : ℝ ↦ f (center + u))
          (f' (center + t)) t := by
      simpa [Function.comp_def] using
        (hfplus t ht).scomp t hinnerPlus
    have hsum := hminus.fun_add hplus
    have hconst := hsum.sub_const (2 * f center)
    simpa [g, d, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hconst
  have ha : ∀ t : ℝ, HasDerivAt a (q t) t := by
    intro t
    simpa [a, q] using ((hasDerivAt_id t).pow 2).const_mul C
  have hga : ∀ t ∈ Set.Icc (0 : ℝ) radius, g t ≤ a t := by
    apply image_le_of_deriv_right_le_deriv_boundary
      (f := g) (f' := d) (B := a) (B' := q)
    · intro t ht
      exact (hg t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hg t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt
    · dsimp [a, g]
      nlinarith
    · intro t ht
      exact (ha t).continuousAt.continuousWithinAt
    · intro t ht
      exact (ha t).hasDerivWithinAt
    · intro t ht
      exact hdq t (Set.Ico_subset_Icc_self ht)
  have hfinal := hga radius ⟨hradius, le_rfl⟩
  dsimp [a, g] at hfinal
  convert hfinal using 1 <;> ring

end

end CPFormal.Analytic.Cp
