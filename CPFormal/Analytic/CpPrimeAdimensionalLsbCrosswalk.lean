import CPFormal.Analytic.CpGenuineSimpleRootLedgerBound

/-!
# Adimensional prime-LSB crosswalk to centered carry and root tangents

For a prime camera, the normalized LSB rises by `1/(p-1)` at every ordinary
step and drops by exactly `1` at the carry residue.  This module identifies
that adimensional increment with the canonical dual centered-carry axis already
used by the unweighted Bessel realization.

The same two-valued pattern, multiplied by `p-1`, is the coefficient

`1 - p * 1_{carry}`.

Placed on a complete balanced camera block, its Dirichlet transform is exactly
the native Genuine bracket.  Hence the finite centered-carry transform is not a
new regularization: it is the existing finite bracketed chart at every cutoff,
and its analytic limit is the bracketed Dirichlet chart.

Finally, on the open critical strip, the tangent ratio of this centered-carry
transform is exactly the previously certified camera/root tangent ratio.  Thus
the root-tangent scalar data used by the Green/Bessel route are tangents of the
Dirichlet transform of the adimensional carry defect.
-/

open scoped BigOperators Topology ENNReal

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-! ## 1. The adimensional LSB increment -/

/-- Increment of the normalized LSB coordinate on one prime residue cycle.
The zero residue is the wrap/carry step. -/
def primeAdimensionalLsbIncrement
    (p : Nat.Primes) (a : Fin p.1) : ℝ :=
  if a = primeCarryResidueZero p then -1 else ((p : ℝ) - 1)⁻¹

@[simp] theorem primeAdimensionalLsbIncrement_zero
    (p : Nat.Primes) :
    primeAdimensionalLsbIncrement p (primeCarryResidueZero p) = -1 := by
  simp [primeAdimensionalLsbIncrement]

@[simp] theorem primeAdimensionalLsbIncrement_ne_zero
    (p : Nat.Primes) {a : Fin p.1}
    (ha : a ≠ primeCarryResidueZero p) :
    primeAdimensionalLsbIncrement p a = ((p : ℝ) - 1)⁻¹ := by
  simp [primeAdimensionalLsbIncrement, ha]

/-- The centered carry defect is `(p-1)` times the adimensional LSB increment. -/
theorem primeCenteredCarryDefect_eq_scale_mul_lsbIncrement
    (p : Nat.Primes) (a : Fin p.1) :
    primeCenteredCarryDefect p a =
      ((p : ℝ) - 1) * primeAdimensionalLsbIncrement p a := by
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have hpgt : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    linarith
  by_cases ha : a = primeCarryResidueZero p
  · subst a
    rw [primeCenteredCarryDefect_zero, primeAdimensionalLsbIncrement_zero]
    ring
  · rw [primeCenteredCarryDefect_ne_zero p ha,
      primeAdimensionalLsbIncrement_ne_zero p ha]
    field_simp [hp1]

/-- Coordinate formula for the critically dressed centered-carry axis. -/
theorem primeCriticalCenteredCarryAxis_apply
    (p : Nat.Primes) (a : Fin p.1) :
    primeCriticalCenteredCarryAxis p a =
      primeCarryDefectAxisCoefficient p * primeCenteredCarryDefect p a := by
  classical
  simp [primeCriticalCenteredCarryAxis]

/-- Coordinate formula for the dual centered-carry axis. -/
theorem primeCriticalCenteredCarryDualAxis_apply
    (p : Nat.Primes) (a : Fin p.1) :
    primeCriticalCenteredCarryDualAxis p a =
      primeCenteredCarryDefect p a / ((p : ℝ) - 1) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have hpgt : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    linarith
  change ((p : ℝ) / ((p : ℝ) - 1)) *
      primeCriticalCenteredCarryAxis p a = _
  rw [primeCriticalCenteredCarryAxis_apply,
    primeCarryDefectAxisCoefficient_eq_inv]
  field_simp [hp0, hp1]

/-- Exact geometric identification: the dual Bessel axis is the normalized LSB
velocity field of the prime camera. -/
theorem primeAdimensionalLsbIncrement_eq_centeredCarryDualAxis
    (p : Nat.Primes) (a : Fin p.1) :
    primeAdimensionalLsbIncrement p a =
      primeCriticalCenteredCarryDualAxis p a := by
  rw [primeCriticalCenteredCarryDualAxis_apply,
    primeCenteredCarryDefect_eq_scale_mul_lsbIncrement]
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have hpgt : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    linarith
  field_simp [hp1]

/-! ## 2. Centered carry coefficient on a balanced camera block -/

/-- The adimensional LSB increment written on a balanced integer offset.
Offset zero is the unique carry residue in the block. -/
def primeAdimensionalLsbOffsetIncrement
    (p : ℕ) (a : ℤ) : ℝ :=
  if a = 0 then -1 else ((p : ℝ) - 1)⁻¹

/-- Unnormalized centered carry coefficient on a complete balanced block. -/
def primeCenteredCarryOffsetCoefficient
    (p : ℕ) (a : ℤ) : ℂ :=
  if a = 0 then 1 - (p : ℂ) else 1

/-- The block coefficient is exactly `(p-1)` times the adimensional LSB
increment. -/
theorem primeCenteredCarryOffsetCoefficient_eq_scaled_lsbIncrement
    (p : ℕ) (hp : Nat.Prime p) (a : ℤ) :
    primeCenteredCarryOffsetCoefficient p a =
      (((p : ℝ) - 1) * primeAdimensionalLsbOffsetIncrement p a : ℝ) := by
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have hpgt : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    linarith
  by_cases ha : a = 0
  · subst a
    simp [primeCenteredCarryOffsetCoefficient,
      primeAdimensionalLsbOffsetIncrement]
    push_cast
    ring
  · simp [primeCenteredCarryOffsetCoefficient,
      primeAdimensionalLsbOffsetIncrement, ha]
    field_simp [hp1]

/-- Centered-carry transform of one complete balanced camera block. -/
def primeCenteredCarryBlock
    (p : ℕ) (f : ℤ → ℂ) (center : ℤ) : ℂ :=
  ∑ a ∈ CPFormal.Genuine.Cp.fullOffsets p,
    primeCenteredCarryOffsetCoefficient p a * f (center + a)

/-- The centered-carry block is the complete block minus `p` copies of its
center. -/
theorem primeCenteredCarryBlock_eq_centerBlock_sub_p_mul_center
    (p : ℕ) (f : ℤ → ℂ) (center : ℤ) :
    primeCenteredCarryBlock p f center =
      CPFormal.Genuine.Cp.centerBlock p f center - (p : ℂ) * f center := by
  classical
  have hzero := CPFormal.Genuine.Cp.zero_mem_fullOffsets p
  have hsplit := Finset.sum_erase_add
    (CPFormal.Genuine.Cp.fullOffsets p)
    (fun a : ℤ => primeCenteredCarryOffsetCoefficient p a * f (center + a))
    hzero
  rw [primeCenteredCarryBlock, ← hsplit,
    CPFormal.Genuine.Cp.fullOffsets_erase_zero]
  have hlegs :
      (∑ a ∈ CPFormal.Genuine.Cp.balancedOffsets p,
        primeCenteredCarryOffsetCoefficient p a * f (center + a)) =
      CPFormal.Genuine.Cp.legSum p f center := by
    unfold CPFormal.Genuine.Cp.legSum
    apply Finset.sum_congr rfl
    intro a ha
    have hane : a ≠ 0 := by
      intro hazero
      subst a
      exact CPFormal.Genuine.Cp.zero_not_mem_balancedOffsets p ha
    simp [primeCenteredCarryOffsetCoefficient, hane]
  rw [hlegs]
  simp [primeCenteredCarryOffsetCoefficient,
    CPFormal.Genuine.Cp.centerBlock_eq_legSum_add_center]
  ring

/-- On a prime camera, the centered-carry block is exactly the native Genuine
bracket. -/
theorem primeCenteredCarryBlock_eq_genuineBracket
    (p : ℕ) (hp : Nat.Prime p) (f : ℤ → ℂ) (center : ℤ) :
    primeCenteredCarryBlock p f center =
      CPFormal.Genuine.Cp.bracket p f center := by
  rw [primeCenteredCarryBlock_eq_centerBlock_sub_p_mul_center,
    ← CPFormal.Genuine.Cp.bracket_eq_centerBlock_sub_p_mul_center
      p hp f center]

/-! ## 3. Finite and infinite centered-carry Dirichlet transforms -/

/-- Finite Dirichlet transform of the centered carry coefficient, including the
native seed and the first `M` complete camera blocks. -/
def finitePrimeCenteredCarryDirichletTransform
    (p M : ℕ) (s : ℂ) : ℂ :=
  CPFormal.Genuine.Cp.seedSum p (dirichletTerm s) +
    ∑ k ∈ Finset.range M,
      primeCenteredCarryBlock p (dirichletTerm s)
        (CPFormal.Genuine.Cp.alignedCenter p k)

/-- Every finite centered-carry transform is literally the finite Genuine
chart. -/
theorem finitePrimeCenteredCarryDirichletTransform_eq_finiteChart
    (p M : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    finitePrimeCenteredCarryDirichletTransform p M s =
      CPFormal.Genuine.Cp.finiteChart p M (dirichletTerm s) := by
  unfold finitePrimeCenteredCarryDirichletTransform
    CPFormal.Genuine.Cp.finiteChart
  apply congrArg (fun tail : ℂ =>
    CPFormal.Genuine.Cp.seedSum p (dirichletTerm s) + tail)
  apply Finset.sum_congr rfl
  intro k hk
  exact primeCenteredCarryBlock_eq_genuineBracket
    p hp (dirichletTerm s) (CPFormal.Genuine.Cp.alignedCenter p k)

/-- For an odd prime, the same finite transform is the analytic finite
bracketed chart. -/
theorem finitePrimeCenteredCarryDirichletTransform_eq_finiteBracketedChart
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) (s : ℂ) :
    finitePrimeCenteredCarryDirichletTransform p M s =
      finiteBracketedDirichletChart p M s := by
  calc
    finitePrimeCenteredCarryDirichletTransform p M s =
        CPFormal.Genuine.Cp.finiteChart p M (dirichletTerm s) :=
      finitePrimeCenteredCarryDirichletTransform_eq_finiteChart p M hp s
    _ = finiteBracketedDirichletChart p M s :=
      (finiteBracketedDirichletChart_eq_finiteChart p M hp hpodd s).symm

/-- Analytic centered-carry Dirichlet transform.  The preceding theorem proves
that its finite approximants are the literal adimensional carry transforms. -/
def primeCenteredCarryDirichletTransform
    (p : ℕ) (s : ℂ) : ℂ :=
  bracketedDirichletChart p s

/-- The finite adimensional carry transforms converge to the analytic transform
throughout the bracket half-plane. -/
theorem finitePrimeCenteredCarryDirichletTransform_tendsto
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {s : ℂ} (hs : -1 < s.re) :
    Tendsto
      (fun M : ℕ => finitePrimeCenteredCarryDirichletTransform p M s)
      atTop (nhds (primeCenteredCarryDirichletTransform p s)) := by
  simpa [primeCenteredCarryDirichletTransform] using
    (finiteBracketedDirichletChart_tendsto p hp hs).congr'
      (Eventually.of_forall fun M =>
        finitePrimeCenteredCarryDirichletTransform_eq_finiteBracketedChart
          p M hp hpodd s)

/-- On the open critical strip, the analytic centered-carry transform is the
camera product `F_p * G`. -/
theorem primeCenteredCarryDirichletTransform_eq_genuinePrimeCameraProduct
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    primeCenteredCarryDirichletTransform p s =
      genuinePrimeCameraProduct p s := by
  unfold primeCenteredCarryDirichletTransform
  exact (genuinePrimeCameraProduct_eq_bracketedDirichletChart
    p hp hpodd hs).symm

/-! ## 4. Root tangent and scalar tests -/

/-- Root tangent ratio written intrinsically from the centered-carry Dirichlet
transform. -/
def primeCenteredCarryRootTangentRatio
    (p : ℕ) (s : ℂ) : ℂ :=
  deriv (primeCenteredCarryDirichletTransform p) s /
    deriv genuineContinuation s

/-- On the strip, the centered-carry tangent ratio is the existing camera/root
tangent ratio. -/
theorem primeCenteredCarryRootTangentRatio_eq_genuineRootCameraTangentRatio
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    primeCenteredCarryRootTangentRatio p s =
      genuineRootCameraTangentRatio p s := by
  have hevent :
      primeCenteredCarryDirichletTransform p =ᶠ[𝓝 s]
        genuinePrimeCameraProduct p := by
    filter_upwards [isOpen_genuineCriticalStrip.mem_nhds hs] with z hz
    exact primeCenteredCarryDirichletTransform_eq_genuinePrimeCameraProduct
      p hp hpodd hz
  unfold primeCenteredCarryRootTangentRatio genuineRootCameraTangentRatio
  rw [EventuallyEq.deriv_eq hevent]

/-- At a simple Genuine zero, the tangent of the centered-carry transform
recovers the camera factor exactly. -/
theorem primeCenteredCarryRootTangentRatio_eq_factor_of_simple_zero
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {s : ℂ} (hroot : IsSimpleGenuineZeroInStrip s) :
    primeCenteredCarryRootTangentRatio p s = cpChartFactor p s := by
  rw [primeCenteredCarryRootTangentRatio_eq_genuineRootCameraTangentRatio
    p hp hpodd hroot.1]
  exact genuineRootCameraTangentRatio_eq_factor
    p hp hroot.1 hroot.2.1 hroot.2.2

/-- Reflected radial profile reconstructed from the tangents of the centered
carry transforms. -/
def primeCenteredCarryRootTangentGreenRadialProfile
    (p : Nat.Primes) (s : ℂ) : ℂ :=
  (((primeCarryAmplitudeRatio p : ℝ) : ℂ) *
      cpPhaseNormalizer (p : ℕ) s / ((p : ℕ) : ℂ)) *
    (primeCenteredCarryRootTangentRatio (p : ℕ) s -
      primeCenteredCarryRootTangentRatio
        (p : ℕ) (reflectedParameter s))

/-- For an odd prime and a simple root, the LSB-centered tangent profile is the
existing root-tangent Green radial profile. -/
theorem primeCenteredCarryRootTangentGreenRadialProfile_eq
    (p : Nat.Primes) (hpodd : Odd (p : ℕ))
    {s : ℂ} (hroot : IsSimpleGenuineZeroInStrip s) :
    primeCenteredCarryRootTangentGreenRadialProfile p s =
      genuineRootTangentGreenRadialProfile p s := by
  have href := isSimpleGenuineZeroInStrip_reflected hroot
  unfold primeCenteredCarryRootTangentGreenRadialProfile
    genuineRootTangentGreenRadialProfile
  rw [primeCenteredCarryRootTangentRatio_eq_genuineRootCameraTangentRatio
      (p : ℕ) p.prop hpodd hroot.1,
    primeCenteredCarryRootTangentRatio_eq_genuineRootCameraTangentRatio
      (p : ℕ) p.prop hpodd href.1]

/-- Green bulk reconstructed from the adimensional centered-carry transform. -/
def primeCenteredCarryRootTangentGreenBulk
    (p : Nat.Primes) (M : ℕ) (s : ℂ) : ℝ :=
  (primeCenteredCarryRootTangentGreenRadialProfile p s).re *
    (finiteReflectedGradientPairing M s).re

/-- At a simple root, the LSB-centered tangent bulk is the existing root-tangent
bulk. -/
theorem primeCenteredCarryRootTangentGreenBulk_eq
    (p : Nat.Primes) (hpodd : Odd (p : ℕ))
    (M : ℕ) {s : ℂ} (hroot : IsSimpleGenuineZeroInStrip s) :
    primeCenteredCarryRootTangentGreenBulk p M s =
      genuineRootTangentGreenBulk p M s := by
  unfold primeCenteredCarryRootTangentGreenBulk genuineRootTangentGreenBulk
  rw [primeCenteredCarryRootTangentGreenRadialProfile_eq p hpodd hroot]

/-- The enriched Bessel scalar test is a weighted sum of tangents of the
adimensional centered-carry Dirichlet transforms, for an atlas of odd prime
cameras. -/
theorem canonicalEnrichedGpreLogJetGreenScalarTest_eq_lsbRootTangent
    (M : ℕ) (S : Finset Nat.Primes) (coeff : Nat.Primes → ℝ)
    {s : ℂ} (hroot : IsSimpleGenuineZeroInStrip s)
    (hodd : ∀ p : Nat.Primes, p ∈ S → Odd (p : ℕ)) :
    canonicalEnrichedGpreLogJetGreenScalarTest M s S coeff =
      ∑ p ∈ S,
        coeff p * primeCenteredCarryRootTangentGreenBulk p (3 * M) s := by
  unfold canonicalEnrichedGpreLogJetGreenScalarTest
  apply Finset.sum_congr rfl
  intro p hpS
  rw [finiteEnrichedNativeGpreLogJetGreenBulkReadout_eq_rootTangent
      p M (by norm_num) (fun _ => 1) (by intro m; norm_num)
      hroot.1 hroot.2.1 hroot.2.2
      (deriv_genuineContinuation_reflectedParameter_ne_zero_of_simple_zero
        hroot.1 hroot.2.1 hroot.2.2),
    primeCenteredCarryRootTangentGreenBulk_eq p (hodd p hpS)
      (3 * M) hroot]

end

end CPFormal.Analytic.Cp
