import CPFormal.Analytic.CpCarryWeightedVerticalBracketTrace
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# No-go: the dressed vertical bracket is not the self-adjoint spectral operator

In amplitude coordinates the interior recurrence has asymmetric neighbouring
coefficients

`q^(-1)` forward and `q` backward.

For the material range `0 < q < 1`, the corresponding bounded operator on the
standard amplitude Hilbert space `ell^2(N,C)` is not symmetric.  This is
witnessed already by the basis vectors at levels `1` and `2`.

Thus the dressed bracket belongs to the TFVD reconstruction/equation channel;
it cannot be silently reused as the fixed self-adjoint operator whose
characteristic parameter is the complex carry time.  The spectral operator
must instead come from the logarithmic phase generator together with the
Green-symmetric boundary restriction.
-/

open scoped ComplexConjugate InnerProduct lp

namespace CPFormal.Analytic.Cp

noncomputable section

/-- First positive vertical basis vector. -/
def carryVerticalBasisOne : CarryVerticalL2 :=
  lp.single 2 1 (1 : ℂ)

/-- Second positive vertical basis vector. -/
def carryVerticalBasisTwo : CarryVerticalL2 :=
  lp.single 2 2 (1 : ℂ)

/-- The forward matrix coefficient of the dressed bracket is `q`. -/
theorem inner_bracket_basisOne_basisTwo
    (q : ℝ) :
    inner ℂ
        (carryWeightedVerticalCenteredBracket q carryVerticalBasisOne)
        carryVerticalBasisTwo = (q : ℂ) := by
  unfold carryVerticalBasisTwo
  rw [lp.inner_single_right]
  change inner ℂ
      (carryWeightedVerticalCenteredBracket q carryVerticalBasisOne 2) 1 = _
  rw [show 2 = 1 + 1 by norm_num,
    carryWeightedVerticalCenteredBracket_succ]
  simp [carryVerticalBasisOne, lp.single_apply, RCLike.inner_apply]

/-- The reverse matrix coefficient is `q^(-1)`. -/
theorem inner_basisOne_bracket_basisTwo
    (q : ℝ) :
    inner ℂ carryVerticalBasisOne
        (carryWeightedVerticalCenteredBracket q carryVerticalBasisTwo) =
      ((q : ℂ)⁻¹) := by
  unfold carryVerticalBasisOne
  rw [lp.inner_single_left]
  change inner ℂ 1
      (carryWeightedVerticalCenteredBracket q carryVerticalBasisTwo 1) = _
  rw [show 1 = 0 + 1 by norm_num,
    carryWeightedVerticalCenteredBracket_succ]
  simp [carryVerticalBasisTwo, lp.single_apply, RCLike.inner_apply]

/-- For `0 < q < 1`, the dressed vertical bracket is not symmetric on the
standard amplitude Hilbert space. -/
theorem carryWeightedVerticalCenteredBracket_not_isSymmetric
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    ¬ (carryWeightedVerticalCenteredBracket q).toLinearMap.IsSymmetric := by
  intro hsym
  have hpair := hsym carryVerticalBasisOne carryVerticalBasisTwo
  change
    inner ℂ
        (carryWeightedVerticalCenteredBracket q carryVerticalBasisOne)
        carryVerticalBasisTwo =
      inner ℂ carryVerticalBasisOne
        (carryWeightedVerticalCenteredBracket q carryVerticalBasisTwo)
    at hpair
  rw [inner_bracket_basisOne_basisTwo,
    inner_basisOne_bracket_basisTwo] at hpair
  have hqeq : q = q⁻¹ := by
    have hre := congrArg Complex.re hpair
    simpa using hre
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hsq : q ^ 2 = 1 := by
    calc
      q ^ 2 = q * q := by ring
      _ = q⁻¹ * q := by rw [hqeq]
      _ = 1 := inv_mul_cancel₀ hqne
  nlinarith

end

end CPFormal.Analytic.Cp
