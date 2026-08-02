import CPFormal.Analytic.CpGenuineQuotient
import CPFormal.Analytic.CpDirichletLimit

/-!
# Bridge factor between the paired Genuine target and the canonical Genuine

The paired-channel Genuine target (the `book-cash` object of the coercive route)
and the canonical `genuineContinuation` of the open critical strip differ, on
that strip, only by an explicit factor

`C(s) = 2 q^2 (1 - 2q) / (1 - q)`, with `q = 2^(-1-s)`.

This module isolates that factor and proves it never vanishes on the open
critical strip.  Consequently, multiplying by `C` transports zero-location
statements between the two targets.  Only the elementary factor is developed
here; the full continuation identity is a separate step.
-/

open Complex

namespace CPFormal.Analytic.Cp

noncomputable section

/-- The vertical ratio `q = 2^(-1-s)`, reused as the bridge variable. -/
def pairedBridgeRatio (s : ℂ) : ℂ := (2 : ℂ) ^ (-1 - s)

/-- Explicit bridge factor `C(s) = 2 q^2 (1 - 2q) / (1 - q)`, `q = 2^(-1-s)`. -/
def pairedBridgeFactor (s : ℂ) : ℂ :=
  2 * pairedBridgeRatio s ^ 2 * (1 - 2 * pairedBridgeRatio s) /
    (1 - pairedBridgeRatio s)

/-- Exact modulus of the bridge variable. -/
theorem norm_pairedBridgeRatio (s : ℂ) :
    ‖pairedBridgeRatio s‖ = (2 : ℝ) ^ (-1 - s.re) := by
  have h := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) (-1 - s)
  simpa [pairedBridgeRatio] using h

/-- On the open critical strip the bridge variable is a strict contraction. -/
theorem norm_pairedBridgeRatio_lt_one {s : ℂ} (hs : 0 < s.re) :
    ‖pairedBridgeRatio s‖ < 1 := by
  rw [norm_pairedBridgeRatio]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

/-- On the open critical strip the doubled bridge variable is still contractive. -/
theorem norm_two_mul_pairedBridgeRatio_lt_one {s : ℂ} (hs : 0 < s.re) :
    ‖2 * pairedBridgeRatio s‖ < 1 := by
  rw [norm_mul, norm_pairedBridgeRatio, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  have hrpow : (2 : ℝ) * (2 : ℝ) ^ (-1 - s.re) = (2 : ℝ) ^ (-s.re) := by
    calc
      (2 : ℝ) * (2 : ℝ) ^ (-1 - s.re)
          = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-1 - s.re) := by rw [Real.rpow_one]
      _ = (2 : ℝ) ^ ((1 : ℝ) + (-1 - s.re)) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ = (2 : ℝ) ^ (-s.re) := by ring_nf
  rw [hrpow]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

/-- The bridge variable is never zero. -/
theorem pairedBridgeRatio_ne_zero (s : ℂ) : pairedBridgeRatio s ≠ 0 := by
  have hpos : (0 : ℝ) < ‖pairedBridgeRatio s‖ := by
    rw [norm_pairedBridgeRatio]; positivity
  intro h
  rw [h, norm_zero] at hpos
  exact lt_irrefl 0 hpos

/-- `1 - q ≠ 0` on the open critical strip. -/
theorem one_sub_pairedBridgeRatio_ne_zero {s : ℂ} (hs : 0 < s.re) :
    1 - pairedBridgeRatio s ≠ 0 := by
  have hlt := norm_pairedBridgeRatio_lt_one hs
  intro h
  rw [sub_eq_zero] at h
  rw [← h, norm_one] at hlt
  exact lt_irrefl 1 hlt

/-- `1 - 2q ≠ 0` on the open critical strip. -/
theorem one_sub_two_mul_pairedBridgeRatio_ne_zero {s : ℂ} (hs : 0 < s.re) :
    1 - 2 * pairedBridgeRatio s ≠ 0 := by
  have hlt := norm_two_mul_pairedBridgeRatio_lt_one hs
  intro h
  rw [sub_eq_zero] at h
  rw [← h, norm_one] at hlt
  exact lt_irrefl 1 hlt

/-- The bridge factor never vanishes on the open critical strip. -/
theorem pairedBridgeFactor_ne_zero {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    pairedBridgeFactor s ≠ 0 := by
  obtain ⟨hpos, _⟩ := hs
  rw [pairedBridgeFactor]
  refine div_ne_zero ?_ (one_sub_pairedBridgeRatio_ne_zero hpos)
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_)
    (one_sub_two_mul_pairedBridgeRatio_ne_zero hpos)
  exact pow_ne_zero 2 (pairedBridgeRatio_ne_zero s)

/-! ## The native paired odd–even channel -/

/-- The paired odd–even term `(2n+1)^(-s) - (2n+2)^(-s)`. -/
def pairedAltTerm (s : ℂ) (n : ℕ) : ℂ :=
  ((2 * n + 1 : ℕ) : ℂ) ^ (-s) - ((2 * n + 2 : ℕ) : ℂ) ^ (-s)

/-- The paired odd–even channel `∑ₙ ((2n+1)^(-s) - (2n+2)^(-s))`. -/
def pairedAltChannel (s : ℂ) : ℂ := ∑' n : ℕ, pairedAltTerm s n

/-- For `1 < re s` the positive monomials are summable. -/
theorem summable_cpow_neg_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => (n : ℂ) ^ (-s)) := by
  have h := (Complex.summable_one_div_nat_cpow (p := s)).mpr hs
  refine h.congr (fun n => ?_)
  rw [Complex.cpow_neg, one_div]

/-- Closed form of the paired channel for `1 < re s`:
`pairedAltChannel s = (1 - 2^(1-s)) * genuineDirichlet s`. -/
theorem pairedAltChannel_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    pairedAltChannel s = (1 - (2 : ℂ) ^ (1 - s)) * genuineDirichlet s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp only [Complex.zero_re] at hs
    linarith
  set f : ℕ → ℂ := fun n => (n : ℂ) ^ (-s) with hf_def
  have hf : Summable f := summable_cpow_neg_of_one_lt_re hs
  have hinj2 : Function.Injective (fun k : ℕ => 2 * k) := by
    intro a b h; dsimp only [] at h; omega
  have hinj_odd : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b h; dsimp only [] at h; omega
  have hinj_2p2 : Function.Injective (fun k : ℕ => 2 * k + 2) := by
    intro a b h; dsimp only [] at h; omega
  have heven : Summable (fun k : ℕ => f (2 * k)) := hf.comp_injective hinj2
  have hodd : Summable (fun k : ℕ => f (2 * k + 1)) := hf.comp_injective hinj_odd
  have hsum_2p2 : Summable (fun k : ℕ => f (2 * k + 2)) :=
    hf.comp_injective hinj_2p2
  have hdouble : ∀ k : ℕ, f (2 * k) = (2 : ℂ) ^ (-s) * f k := by
    intro k
    simp only [hf_def]
    rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow, Nat.cast_ofNat]
  have h2p2 : ∀ n : ℕ, f (2 * n + 2) = (2 : ℂ) ^ (-s) * f (n + 1) := by
    intro n
    have hd := hdouble (n + 1)
    have he : 2 * (n + 1) = 2 * n + 2 := by omega
    rwa [he] at hd
  have hf0 : f 0 = 0 := by
    simp only [hf_def, Nat.cast_zero]
    exact Complex.zero_cpow (neg_ne_zero.mpr hs0)
  have hgen : genuineDirichlet s = ∑' k : ℕ, f (k + 1) := by
    rw [genuineDirichlet]
    refine tsum_congr (fun k => ?_)
    simp only [hf_def, dirichletTerm]
    norm_cast
  have hsum_shift : (∑' n : ℕ, f (n + 1)) = (∑' k : ℕ, f k) := by
    rw [hf.tsum_eq_zero_add, hf0, zero_add]
  have hSgen : (∑' k : ℕ, f k) = genuineDirichlet s := by
    rw [hf.tsum_eq_zero_add, hf0, zero_add, ← hgen]
  have hev : (∑' k : ℕ, f (2 * k)) = (2 : ℂ) ^ (-s) * (∑' k : ℕ, f k) := by
    rw [tsum_congr hdouble, tsum_mul_left]
  have hodd_val :
      (∑' k : ℕ, f (2 * k + 1)) = (1 - (2 : ℂ) ^ (-s)) * (∑' k : ℕ, f k) := by
    have hsplit := tsum_even_add_odd heven hodd
    rw [hev] at hsplit
    linear_combination hsplit
  have h2p2sum :
      (∑' n : ℕ, f (2 * n + 2)) = (2 : ℂ) ^ (-s) * (∑' k : ℕ, f k) := by
    rw [tsum_congr h2p2, tsum_mul_left, hsum_shift]
  have two_mul_cpow : (2 : ℂ) * (2 : ℂ) ^ (-s) = (2 : ℂ) ^ (1 - s) := by
    rw [show (1 : ℂ) - s = 1 + (-s) by ring,
      Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_one]
  have hterm : ∀ n : ℕ, pairedAltTerm s n = f (2 * n + 1) - f (2 * n + 2) := by
    intro n; simp only [pairedAltTerm, hf_def]
  calc
    pairedAltChannel s
        = ∑' n : ℕ, (f (2 * n + 1) - f (2 * n + 2)) := by
          unfold pairedAltChannel; exact tsum_congr hterm
    _ = (∑' n : ℕ, f (2 * n + 1)) - (∑' n : ℕ, f (2 * n + 2)) :=
          hodd.tsum_sub hsum_2p2
    _ = (1 - (2 : ℂ) ^ (-s)) * (∑' k : ℕ, f k) -
          (2 : ℂ) ^ (-s) * (∑' k : ℕ, f k) := by rw [hodd_val, h2p2sum]
    _ = (1 - 2 * (2 : ℂ) ^ (-s)) * (∑' k : ℕ, f k) := by ring
    _ = (1 - (2 : ℂ) ^ (1 - s)) * (∑' k : ℕ, f k) := by rw [two_mul_cpow]
    _ = (1 - (2 : ℂ) ^ (1 - s)) * genuineDirichlet s := by rw [hSgen]

end

end CPFormal.Analytic.Cp
