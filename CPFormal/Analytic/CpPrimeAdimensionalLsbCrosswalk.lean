import CPFormal.Analytic.CpGenuineSimpleRootLedgerBound

/-!
# Adimensional prime-LSB crosswalk

The normalized LSB of a prime camera rises by `1/(p-1)` on an ordinary step
and drops by exactly `1` at the wrap/carry residue.  This file identifies that
velocity field with the canonical dual centered-carry axis used by the
unweighted Bessel construction.

The unnormalized two-valued coefficient is `1 - p * 1_{carry}`.  Its
Dirichlet transform on every complete balanced camera block is exactly the
native Genuine bracket.  Hence the finite transform is the existing finite
bracketed chart, and its analytic tangent at a simple root is the existing
camera/root tangent ratio.
-/

open scoped BigOperators Topology ENNReal

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-! ## Adimensional LSB velocity and the dual Bessel axis -/

/-- Velocity of the normalized LSB on one prime residue cycle. -/
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

/-- The centered carry defect is `(p-1)` times the LSB velocity. -/
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
  simp only [primeCriticalCenteredCarryAxis, lp.coeFn_sum,
    Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single]
  simp

/-- Coordinate formula for the canonical dual axis. -/
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

/-- Exact identification: the dual Bessel axis is the adimensional LSB
velocity field. -/
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

/-! ## Centered carry transform on complete camera blocks -/

/-- Unnormalized centered carry coefficient on a balanced integer block. -/
def primeCenteredCarryOffsetCoefficient
    (p : ℕ) (a : ℤ) : ℂ :=
  if a = 0 then 1 - (p : ℂ) else 1

@[simp] theorem primeCenteredCarryOffsetCoefficient_zero
    (p : ℕ) :
    primeCenteredCarryOffsetCoefficient p 0 = 1 - (p : ℂ) := by
  simp [primeCenteredCarryOffsetCoefficient]

@[simp] theorem primeCenteredCarryOffsetCoefficient_ne_zero
    (p : ℕ) {a : ℤ} (ha : a ≠ 0) :
    primeCenteredCarryOffsetCoefficient p a = 1 := by
  simp [primeCenteredCarryOffsetCoefficient, ha]

/-- Centered carry transform of one complete balanced camera block. -/
def primeCenteredCarryBlock
    (p : ℕ) (f : ℤ → ℂ) (center : ℤ) : ℂ :=
  ∑ a ∈ CPFormal.Genuine.Cp.fullOffsets p,
    primeCenteredCarryOffsetCoefficient p a * f (center + a)

/-- The block transform is the complete block minus `p` center copies. -/
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
    simp [hane]
  rw [hlegs]
  simp [CPFormal.Genuine.Cp.centerBlock_eq_legSum_add_center]
  ring

/-- For a prime camera, the block transform is exactly its Genuine bracket. -/
theorem primeCenteredCarryBlock_eq_genuineBracket
    (p : ℕ) (hp : Nat.Prime p) (f : ℤ → ℂ) (center : ℤ) :
    primeCenteredCarryBlock p f center =
      CPFormal.Genuine.Cp.bracket p f center := by
  rw [primeCenteredCarryBlock_eq_centerBlock_sub_p_mul_center,
    ← CPFormal.Genuine.Cp.bracket_eq_centerBlock_sub_p_mul_center
      p hp f center]

/-! ## Finite transform, analytic limit, and root tangent -/

/-- Seed plus the first `M` centered-carry Dirichlet blocks. -/
def finitePrimeCenteredCarryDirichletTransform
    (p M : ℕ) (s : ℂ) : ℂ :=
  CPFormal.Genuine.Cp.seedSum p (dirichletTerm s) +
    ∑ k ∈ Finset.range M,
      primeCenteredCarryBlock p (dirichletTerm s)
        (CPFormal.Genuine.Cp.alignedCenter p k)

/-- The finite centered-carry transform is literally the finite Genuine chart. -/
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

/-- For an odd prime, it is also the analytic finite bracketed chart. -/
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

/-- Analytic continuation of the centered-carry Dirichlet transform. -/
def primeCenteredCarryDirichletTransform
    (p : ℕ) (s : ℂ) : ℂ :=
  bracketedDirichletChart p s

/-- Finite centered-carry transforms converge throughout `re(s)>-1`. -/
theorem finitePrimeCenteredCarryDirichletTransform_tendsto
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {s : ℂ} (hs : -1 < s.re) :
    Tendsto
      (fun M : ℕ => finitePrimeCenteredCarryDirichletTransform p M s)
      atTop (nhds (primeCenteredCarryDirichletTransform p s)) := by
  have hlimit := finiteBracketedDirichletChart_tendsto p hp hs
  have heq :
      (fun M : ℕ => finiteBracketedDirichletChart p M s) =ᶠ[atTop]
        (fun M : ℕ => finitePrimeCenteredCarryDirichletTransform p M s) :=
    Eventually.of_forall fun M =>
      (finitePrimeCenteredCarryDirichletTransform_eq_finiteBracketedChart
        p M hp hpodd s).symm
  simpa [primeCenteredCarryDirichletTransform] using hlimit.congr' heq

/-- On the strip, the centered-carry transform is the camera product `F_p G`. -/
theorem primeCenteredCarryDirichletTransform_eq_genuinePrimeCameraProduct
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    primeCenteredCarryDirichletTransform p s =
      genuinePrimeCameraProduct p s := by
  unfold primeCenteredCarryDirichletTransform
  exact (genuinePrimeCameraProduct_eq_bracketedDirichletChart
    p hp hpodd hs).symm

/-- Root tangent ratio of the centered-carry transform. -/
def primeCenteredCarryRootTangentRatio
    (p : ℕ) (s : ℂ) : ℂ :=
  deriv (primeCenteredCarryDirichletTransform p) s /
    deriv genuineContinuation s

/-- Its root tangent is the existing camera/root tangent. -/
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

/-- At a simple Genuine zero, the tangent recovers the camera factor exactly. -/
theorem primeCenteredCarryRootTangentRatio_eq_factor_of_simple_zero
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {s : ℂ} (hroot : IsSimpleGenuineZeroInStrip s) :
    primeCenteredCarryRootTangentRatio p s = cpChartFactor p s := by
  rw [primeCenteredCarryRootTangentRatio_eq_genuineRootCameraTangentRatio
    p hp hpodd hroot.1]
  exact genuineRootCameraTangentRatio_eq_factor
    p hp hroot.1 hroot.2.1 hroot.2.2.1

end

end CPFormal.Analytic.Cp
