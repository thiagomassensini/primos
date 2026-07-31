import CPFormal.Analytic.CpGenuineQuotient

/-!
# Camera factors without a primality assumption

The primitive finite scanner uses two geometries.

* An odd width `b = 2h + 1` tiles a complete block and has factor
  `1 - b^(1-s)`.
* An even natural width `b = 2a` omits the middle congruence class and has
  factor
  `1 - a^(-s) - (b-2)b^(-s)`.

This file isolates the regularity statements that depend only on these
factors.  It does not identify a finite chart with either factor; that
combinatorial statement belongs to the finite-camera algebra module.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/--
The odd-camera factor is the usual `Cp` factor, now read for an arbitrary
nondegenerate natural width rather than only for a prime.
-/
abbrev naturalOddCameraFactor (b : ℕ) (s : ℂ) : ℂ :=
  cpChartFactor b s

/--
Factor forced by the exact finite normal form of an even natural camera
`b = 2a`.
-/
def naturalEvenCameraFactor (b : ℕ) (s : ℂ) : ℂ :=
  1 -
    ((b / 2 : ℕ) : ℂ) ^ (-s) -
      ((b - 2 : ℕ) : ℂ) * (b : ℂ) ^ (-s)

/-- Complex parameter packaged by the native real rotating state. -/
def nativeCarryCriticalParameter (time : ℝ) : ℂ :=
  ⟨(1 : ℝ) / 2, time⟩

@[simp] theorem nativeCarryCriticalParameter_re (time : ℝ) :
    (nativeCarryCriticalParameter time).re = (1 : ℝ) / 2 := by
  rfl

@[simp] theorem nativeCarryCriticalParameter_im (time : ℝ) :
    (nativeCarryCriticalParameter time).im = time := by
  rfl

/-- Exact norm of the power used by an arbitrary positive camera width. -/
theorem norm_nat_cpow_one_sub
    (b : ℕ) (hb : 0 < b) (s : ℂ) :
    ‖(b : ℂ) ^ (1 - s)‖ = (b : ℝ) ^ (1 - s.re) := by
  have hbReal : 0 < (b : ℝ) := by
    exact_mod_cast hb
  simpa using
    (Complex.norm_cpow_eq_rpow_re_of_pos hbReal (1 - s))

/--
Below `re(s)=1`, the odd-camera power has norm greater than one for every
natural width `b > 1`.  Primality is irrelevant.
-/
theorem nat_cpow_one_sub_ne_one_of_re_lt_one
    (b : ℕ) (hb : 1 < b) {s : ℂ} (hs : s.re < 1) :
    (b : ℂ) ^ (1 - s) ≠ 1 := by
  intro hpower
  have hnorm := congrArg norm hpower
  rw [norm_nat_cpow_one_sub b (by omega) s, norm_one] at hnorm
  have hbReal : (1 : ℝ) < (b : ℝ) := by
    exact_mod_cast hb
  have hexponent : 0 < (1 : ℝ) - s.re := by
    linarith
  have hstrict := Real.one_lt_rpow hbReal hexponent
  linarith

/--
Above `re(s)=1`, the same power has norm less than one for every natural
width `b > 1`.
-/
theorem nat_cpow_one_sub_ne_one_of_one_lt_re
    (b : ℕ) (hb : 1 < b) {s : ℂ} (hs : 1 < s.re) :
    (b : ℂ) ^ (1 - s) ≠ 1 := by
  intro hpower
  have hnorm := congrArg norm hpower
  rw [norm_nat_cpow_one_sub b (by omega) s, norm_one] at hnorm
  have hbReal : (1 : ℝ) < (b : ℝ) := by
    exact_mod_cast hb
  have hexponent : (1 : ℝ) - s.re < 0 := by
    linarith
  have hstrict := Real.rpow_lt_one_of_one_lt_of_neg hbReal hexponent
  linarith

/--
The factor of every odd natural camera is regular away from `re(s)=1`.

The theorem itself does not need oddness; the hypothesis records the geometry
for which this is the factor selected by the finite normal form.
-/
theorem naturalOddCameraFactor_ne_zero_of_re_ne_one
    (b : ℕ) (_hbodd : Odd b) (hb : 1 < b)
    {s : ℂ} (hs : s.re ≠ 1) :
    naturalOddCameraFactor b s ≠ 0 := by
  rcases lt_or_gt_of_ne hs with hleft | hright
  · intro hzero
    apply nat_cpow_one_sub_ne_one_of_re_lt_one b hb hleft
    exact (sub_eq_zero.mp hzero).symm
  · intro hzero
    apply nat_cpow_one_sub_ne_one_of_one_lt_re b hb hright
    exact (sub_eq_zero.mp hzero).symm

/-- Odd prime and odd composite factors are all nonzero on the critical line. -/
theorem naturalOddCameraFactor_ne_zero_on_criticalLine
    (b : ℕ) (hbodd : Odd b) (hb : 1 < b)
    {s : ℂ} (hs : s.re = (1 : ℝ) / 2) :
    naturalOddCameraFactor b s ≠ 0 := by
  apply naturalOddCameraFactor_ne_zero_of_re_ne_one b hbodd hb
  linarith

/-- Norm of a negative complex power of a positive natural base. -/
theorem norm_nat_cpow_neg
    (b : ℕ) (hb : 0 < b) (s : ℂ) :
    ‖(b : ℂ) ^ (-s)‖ = (b : ℝ) ^ (-s.re) := by
  have hbReal : 0 < (b : ℝ) := by
    exact_mod_cast hb
  simpa using
    (Complex.norm_cpow_eq_rpow_re_of_pos hbReal (-s))

/--
A transparent sufficient condition for regularity of an even-camera factor
on the critical line.

The rightmost center channel must dominate the unit seed plus the omitted
middle-residue channel.  A separate arithmetic lemma can discharge this
inequality uniformly for even `b ≥ 6`; keeping it explicit here prevents a
triangle-inequality argument from being hidden inside the camera definition.
-/
theorem naturalEvenCameraFactor_ne_zero_of_criticalLine_of_domination
    (b : ℕ) (hb : 4 ≤ b)
    {s : ℂ} (hs : s.re = (1 : ℝ) / 2)
    (hdom :
      1 + ((b / 2 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) <
        ((b - 2 : ℕ) : ℝ) * (b : ℝ) ^ (-(1 : ℝ) / 2)) :
    naturalEvenCameraFactor b s ≠ 0 := by
  intro hzero
  have hbpos : 0 < b := by omega
  have hhalfpos : 0 < b / 2 := by omega
  have hnegHalf :
      -((1 : ℝ) / 2) = (-(1 : ℝ)) / 2 := by
    ring
  have heq :
      ((b - 2 : ℕ) : ℂ) * (b : ℂ) ^ (-s) =
        1 - ((b / 2 : ℕ) : ℂ) ^ (-s) := by
    unfold naturalEvenCameraFactor at hzero
    linear_combination -hzero
  have hleft :
      ‖((b - 2 : ℕ) : ℂ) * (b : ℂ) ^ (-s)‖ =
        ((b - 2 : ℕ) : ℝ) * (b : ℝ) ^ (-(1 : ℝ) / 2) := by
    rw [norm_mul, norm_nat_cpow_neg b hbpos s, hs]
    rw [hnegHalf]
    simp
  have hright :
      ‖1 - ((b / 2 : ℕ) : ℂ) ^ (-s)‖ ≤
        1 + ((b / 2 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) := by
    calc
      ‖1 - ((b / 2 : ℕ) : ℂ) ^ (-s)‖ ≤
          ‖(1 : ℂ)‖ + ‖((b / 2 : ℕ) : ℂ) ^ (-s)‖ :=
        norm_sub_le _ _
      _ = 1 + ((b / 2 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) := by
        rw [norm_one,
          norm_nat_cpow_neg (b / 2) hhalfpos s, hs]
        rw [hnegHalf]
  rw [heq] at hleft
  linarith

/--
The exceptional natural width `4` has a useful exact factorization.  This is
also the factor of the scanner's special aligned camera `2`.
-/
theorem naturalEvenCameraFactor_four_eq
    (s : ℂ) :
    naturalEvenCameraFactor 4 s =
      (1 - (2 : ℂ) ^ (1 - s)) * (1 + (2 : ℂ) ^ (-s)) := by
  unfold naturalEvenCameraFactor
  norm_num
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have hlinear :
      (2 : ℂ) ^ (1 - s) =
        (2 : ℂ) * (2 : ℂ) ^ (-s) := by
    simpa [sub_eq_add_neg] using
      (Complex.cpow_add (x := (2 : ℂ)) (1 : ℂ) (-s) htwo)
  have hpow :
      (4 : ℂ) ^ (-s) =
        (2 : ℂ) ^ (-s) * (2 : ℂ) ^ (-s) := by
    convert (Complex.natCast_mul_natCast_cpow 2 2 (-s)) using 1 <;>
      norm_num
  rw [hlinear, hpow]
  ring

/-- The width-`4` factor is nonzero in the open strip `0 < re(s) < 1`. -/
theorem naturalEvenCameraFactor_four_ne_zero_on_openStrip
    {s : ℂ} (hsPos : 0 < s.re) (hsOne : s.re < 1) :
    naturalEvenCameraFactor 4 s ≠ 0 := by
  rw [naturalEvenCameraFactor_four_eq]
  apply mul_ne_zero
  · intro hzero
    apply nat_cpow_one_sub_ne_one_of_re_lt_one 2 (by norm_num) hsOne
    exact (sub_eq_zero.mp hzero).symm
  · intro hzero
    have hpow : (2 : ℂ) ^ (-s) = -1 := by
      linear_combination hzero
    have hnorm := congrArg norm hpow
    have hnormTwo :
        ‖(2 : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-s.re) := by
      simpa using
        (Complex.norm_cpow_eq_rpow_re_of_pos
          (x := (2 : ℝ)) (by norm_num) (-s))
    rw [hnormTwo, norm_neg, norm_one] at hnorm
    have htwo : (1 : ℝ) < 2 := by norm_num
    have hstrict :=
      Real.rpow_lt_one_of_one_lt_of_neg htwo
        (by linarith : -s.re < 0)
    linarith

/-- In particular, the width-`4`/aligned-`C2` factor is regular critically. -/
theorem naturalEvenCameraFactor_four_ne_zero_on_criticalLine
    {s : ℂ} (hs : s.re = (1 : ℝ) / 2) :
    naturalEvenCameraFactor 4 s ≠ 0 :=
  naturalEvenCameraFactor_four_ne_zero_on_openStrip
    (by linarith) (by linarith)

end

end CPFormal.Analytic.Cp
