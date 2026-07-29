import CPFormal.Analytic.CpPositionalCarryQuadraticRigidity
import CPFormal.Analytic.CpNativeCarryRealPlaneBracket

/-!
# Crosswalk between positional carry mass and real-state energy

The mass by carry depth and the inverse-integer energy of the real state are
different pointwise quantities.  Their correct connection is equality of
admissible exponent domains: both compatibility predicates select exactly
`sigma = 1/2`.

This module records that equivalence without asserting the false pointwise
identity `b^(-k) = n^(-1)`.
-/

namespace CPFormal.Analytic.Cp

open CPFormal.Carry.Cp

noncomputable section

/--
Quadratic Domain Crosswalk.

For every nondegenerate positional base, compatibility with carry mass by
depth is equivalent to compatibility with the real rotating state's
inverse-integer energy.  The rotation time is unrestricted.
-/
theorem positionalCarryMassCompatible_iff_realEnergyCompatible
    (b : ℕ) (hb : 1 < b) (sigma time : ℝ) :
    PositionalCarryMassCompatible b sigma ↔
      NativeCarryRealPlaneMassCompatible sigma time := by
  rw [positionalCarryMassCompatible_iff b hb sigma,
    nativeCarryRealPlaneMassCompatible_iff sigma time]

end

end CPFormal.Analytic.Cp
