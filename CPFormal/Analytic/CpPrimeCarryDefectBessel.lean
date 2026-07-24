import CPFormal.Analytic.CpGenuineGprePrimeVerticalTraceWeightedBessel

/-!
# Explicit Bessel family from centered prime carry defects

For a prime camera `p`, the drift-removed carry pulse on one complete residue
cycle is the indicator of the zero residue.  Its centered form is

`phi_p(a) = 1 - p * 1_{a=0}`.

This vector has mean zero and squared norm `p * (p - 1)` for the unnormalized
counting measure.  The local probability normalization contributes one factor
`p^(-1/2)`, while the critical carry amplitude contributes the second.  Thus
the material axis has coefficient `p^(-1)` and squared norm

`(p - 1) / p < 1`.

Different prime cameras are kept on distinct outer Hilbert coordinates.  The
resulting synthesis map satisfies the unweighted Bessel estimate

`||sum_p c_p axis_p||^2 <= sum_p c_p^2`

on every finite prime atlas.  No Genuine zero, Green closure, or critical
localization is used in this finite arithmetic theorem.
-/

open scoped BigOperators ENNReal

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Distinguished zero residue in a prime camera. -/
def primeCarryResidueZero (p : Nat.Primes) : Fin p.1 :=
  ⟨0, p.prop.pos⟩

/-- Binary carry pulse on one complete residue cycle. -/
def primeCarryResiduePulse
    (p : Nat.Primes) (a : Fin p.1) : ℝ :=
  if a = primeCarryResidueZero p then 1 else 0

/-- Centered carry defect: `1 - p` at the carry residue and `1` elsewhere. -/
def primeCenteredCarryDefect
    (p : Nat.Primes) (a : Fin p.1) : ℝ :=
  1 - (p : ℝ) * primeCarryResiduePulse p a

@[simp] theorem primeCenteredCarryDefect_zero
    (p : Nat.Primes) :
    primeCenteredCarryDefect p (primeCarryResidueZero p) =
      1 - (p : ℝ) := by
  simp [primeCenteredCarryDefect, primeCarryResiduePulse]

@[simp] theorem primeCenteredCarryDefect_ne_zero
    (p : Nat.Primes) {a : Fin p.1}
    (ha : a ≠ primeCarryResidueZero p) :
    primeCenteredCarryDefect p a = 1 := by
  simp [primeCenteredCarryDefect, primeCarryResiduePulse, ha]

/-- The carry pulse has total mass one on a complete residue cycle. -/
theorem sum_primeCarryResiduePulse_eq_one
    (p : Nat.Primes) :
    (∑ a : Fin p.1, primeCarryResiduePulse p a) = 1 := by
  classical
  simp [primeCarryResiduePulse]

/-- A constant multiple of the carry pulse integrates to that constant. -/
theorem sum_const_mul_primeCarryResiduePulse_eq
    (p : Nat.Primes) (c : ℝ) :
    (∑ a : Fin p.1, c * primeCarryResiduePulse p a) = c := by
  rw [← Finset.mul_sum, sum_primeCarryResiduePulse_eq_one, mul_one]

/-- The centered defect has zero mean over one full camera cycle. -/
theorem sum_primeCenteredCarryDefect_eq_zero
    (p : Nat.Primes) :
    (∑ a : Fin p.1, primeCenteredCarryDefect p a) = 0 := by
  classical
  unfold primeCenteredCarryDefect
  rw [Finset.sum_sub_distrib]
  have hone : (∑ _a : Fin p.1, (1 : ℝ)) = (p : ℝ) := by simp
  rw [hone, sum_const_mul_primeCarryResiduePulse_eq p (p : ℝ)]
  ring

/-- A binary residue pulse is idempotent under squaring. -/
theorem primeCarryResiduePulse_sq
    (p : Nat.Primes) (a : Fin p.1) :
    (primeCarryResiduePulse p a) ^ 2 = primeCarryResiduePulse p a := by
  classical
  by_cases ha : a = primeCarryResidueZero p <;>
    simp [primeCarryResiduePulse, ha]

/-- Exact squared ledger of one centered carry defect. -/
theorem sum_sq_primeCenteredCarryDefect
    (p : Nat.Primes) :
    (∑ a : Fin p.1, (primeCenteredCarryDefect p a) ^ 2) =
      (p : ℝ) * ((p : ℝ) - 1) := by
  classical
  have hpoint : ∀ a : Fin p.1,
      (primeCenteredCarryDefect p a) ^ 2 =
        1 - 2 * (p : ℝ) * primeCarryResiduePulse p a +
          (p : ℝ) ^ 2 * primeCarryResiduePulse p a := by
    intro a
    unfold primeCenteredCarryDefect
    calc
      (1 - (p : ℝ) * primeCarryResiduePulse p a) ^ 2 =
          1 - 2 * (p : ℝ) * primeCarryResiduePulse p a +
            (p : ℝ) ^ 2 * (primeCarryResiduePulse p a) ^ 2 := by ring
      _ = 1 - 2 * (p : ℝ) * primeCarryResiduePulse p a +
            (p : ℝ) ^ 2 * primeCarryResiduePulse p a := by
              rw [primeCarryResiduePulse_sq]
  calc
    (∑ a : Fin p.1, (primeCenteredCarryDefect p a) ^ 2) =
        ∑ a : Fin p.1,
          (1 - 2 * (p : ℝ) * primeCarryResiduePulse p a +
            (p : ℝ) ^ 2 * primeCarryResiduePulse p a) := by
              apply Finset.sum_congr rfl
              intro a _ha
              exact hpoint a
    _ = (∑ _a : Fin p.1, (1 : ℝ)) -
          (∑ a : Fin p.1,
            (2 * (p : ℝ)) * primeCarryResiduePulse p a) +
          (∑ a : Fin p.1,
            ((p : ℝ) ^ 2) * primeCarryResiduePulse p a) := by
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (p : ℝ) - 2 * (p : ℝ) + (p : ℝ) ^ 2 := by
      have hone : (∑ _a : Fin p.1, (1 : ℝ)) = (p : ℝ) := by simp
      rw [hone,
        sum_const_mul_primeCarryResiduePulse_eq p (2 * (p : ℝ)),
        sum_const_mul_primeCarryResiduePulse_eq p ((p : ℝ) ^ 2)]
    _ = (p : ℝ) * ((p : ℝ) - 1) := by ring

/-- The product of two independent centered camera cycles has zero total
correlation. -/
theorem sum_prod_primeCenteredCarryDefect_eq_zero
    (p q : Nat.Primes) :
    (∑ x : Fin p.1 × Fin q.1,
      primeCenteredCarryDefect p x.1 *
        primeCenteredCarryDefect q x.2) = 0 := by
  rw [Fintype.sum_prod_type]
  calc
    (∑ a : Fin p.1, ∑ b : Fin q.1,
        primeCenteredCarryDefect p a *
          primeCenteredCarryDefect q b) =
      ∑ a : Fin p.1,
        primeCenteredCarryDefect p a *
          (∑ b : Fin q.1, primeCenteredCarryDefect q b) := by
            apply Finset.sum_congr rfl
            intro a _ha
            rw [Finset.mul_sum]
    _ = 0 := by rw [sum_primeCenteredCarryDefect_eq_zero]; simp

/-- Local finite Hilbert space of a prime residue camera. -/
abbrev PrimeCarryResidueHilbert (p : Nat.Primes) :=
  lp (fun _ : Fin p.1 => ℝ) 2

/-- The two factors of `p^(-1/2)`: one is the normalized counting measure of
one residue cycle and one is the critical carry amplitude. -/
def primeCarryDefectAxisCoefficient (p : Nat.Primes) : ℝ :=
  primeCarryAmplitudeRatio p * primeCarryAmplitudeRatio p

@[simp] theorem primeCarryDefectAxisCoefficient_eq_inv
    (p : Nat.Primes) :
    primeCarryDefectAxisCoefficient p = (p : ℝ)⁻¹ := by
  rw [primeCarryDefectAxisCoefficient]
  simpa [pow_two] using primeCarryAmplitudeRatio_sq_eq_inv (p : ℕ)

/-- Material centered carry axis in one camera. -/
def primeCriticalCenteredCarryAxis
    (p : Nat.Primes) : PrimeCarryResidueHilbert p :=
  ∑ a ∈ (Finset.univ : Finset (Fin p.1)),
    lp.single 2 a
      (primeCarryDefectAxisCoefficient p * primeCenteredCarryDefect p a)

/-- Exact local norm: the critically dressed centered axis has norm strictly
below one. -/
theorem primeCriticalCenteredCarryAxis_norm_sq
    (p : Nat.Primes) :
    ‖primeCriticalCenteredCarryAxis p‖ ^ 2 =
      ((p : ℝ) - 1) / (p : ℝ) := by
  have hraw :=
    lp.norm_sum_single
      (E := fun _ : Fin p.1 => ℝ)
      (p := (2 : ℝ≥0∞)) (by norm_num)
      (fun a : Fin p.1 =>
        primeCarryDefectAxisCoefficient p * primeCenteredCarryDefect p a)
      (Finset.univ : Finset (Fin p.1))
  have hraw' :
      ‖primeCriticalCenteredCarryAxis p‖ ^ 2 =
        ∑ a : Fin p.1,
          |primeCarryDefectAxisCoefficient p *
            primeCenteredCarryDefect p a| ^ 2 := by
    simpa [primeCriticalCenteredCarryAxis, Real.norm_eq_abs] using hraw
  calc
    ‖primeCriticalCenteredCarryAxis p‖ ^ 2 =
        ∑ a : Fin p.1,
          (primeCarryDefectAxisCoefficient p *
            primeCenteredCarryDefect p a) ^ 2 := by
              rw [hraw']
              apply Finset.sum_congr rfl
              intro a _ha
              rw [sq_abs]
    _ = (primeCarryDefectAxisCoefficient p) ^ 2 *
          ∑ a : Fin p.1, (primeCenteredCarryDefect p a) ^ 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _ha
            ring
    _ = ((p : ℝ) - 1) / (p : ℝ) := by
      rw [primeCarryDefectAxisCoefficient_eq_inv,
        sum_sq_primeCenteredCarryDefect]
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
      field_simp [hp0]

/-- Local contractivity of every centered carry axis. -/
theorem primeCriticalCenteredCarryAxis_norm_le_one
    (p : Nat.Primes) :
    ‖primeCriticalCenteredCarryAxis p‖ ≤ 1 := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hfrac : ((p : ℝ) - 1) / (p : ℝ) < 1 := by
    rw [div_lt_one hpR]
    linarith
  have hsq := primeCriticalCenteredCarryAxis_norm_sq p
  have hnorm0 : 0 ≤ ‖primeCriticalCenteredCarryAxis p‖ := norm_nonneg _
  nlinarith

/-- Finite orthogonal sum of all residue-camera Hilbert spaces in an atlas. -/
abbrev PrimeCarryDefectAtlasHilbert (S : Finset Nat.Primes) :=
  lp (fun p : S => PrimeCarryResidueHilbert p.1) 2

/-- A local camera axis inserted into its own atlas coordinate. -/
def primeCriticalCenteredCarryAtlasAxis
    (S : Finset Nat.Primes) (p : S) : PrimeCarryDefectAtlasHilbert S :=
  lp.single 2 p (primeCriticalCenteredCarryAxis p.1)

/-- Synthesis of finitely many centered carry axes. -/
def finitePrimeCarryDefectSynthesis
    (S : Finset Nat.Primes) (c : S → ℝ) :
    PrimeCarryDefectAtlasHilbert S :=
  ∑ p ∈ (Finset.univ : Finset S),
    lp.single 2 p (c p • primeCriticalCenteredCarryAxis p.1)

/-- Explicit, unweighted Bessel estimate for every finite prime atlas. -/
theorem finitePrimeCarryDefectSynthesis_norm_sq_le
    (S : Finset Nat.Primes) (c : S → ℝ) :
    ‖finitePrimeCarryDefectSynthesis S c‖ ^ 2 ≤
      ∑ p : S, (c p) ^ 2 := by
  have hraw :=
    lp.norm_sum_single
      (E := fun p : S => PrimeCarryResidueHilbert p.1)
      (p := (2 : ℝ≥0∞)) (by norm_num)
      (fun p : S => c p • primeCriticalCenteredCarryAxis p.1)
      (Finset.univ : Finset S)
  rw [show ‖finitePrimeCarryDefectSynthesis S c‖ ^ 2 =
      ∑ p : S, ‖c p • primeCriticalCenteredCarryAxis p.1‖ ^ 2 by
        simpa [finitePrimeCarryDefectSynthesis] using hraw]
  apply Finset.sum_le_sum
  intro p _hp
  rw [norm_smul, Real.norm_eq_abs]
  have haxis := primeCriticalCenteredCarryAxis_norm_le_one p.1
  have habs0 : 0 ≤ |c p| := abs_nonneg _
  have hnorm0 : 0 ≤ ‖primeCriticalCenteredCarryAxis p.1‖ := norm_nonneg _
  have hmul :
      |c p| * ‖primeCriticalCenteredCarryAxis p.1‖ ≤ |c p| := by
    simpa using mul_le_mul_of_nonneg_left haxis habs0
  have hleft0 :
      0 ≤ |c p| * ‖primeCriticalCenteredCarryAxis p.1‖ :=
    mul_nonneg habs0 hnorm0
  have hsq :
      (|c p| * ‖primeCriticalCenteredCarryAxis p.1‖) ^ 2 ≤
        |c p| ^ 2 :=
    (sq_le_sq₀ hleft0 habs0).2 hmul
  simpa [sq_abs] using hsq

end

end CPFormal.Analytic.Cp
