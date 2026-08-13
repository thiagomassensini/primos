import CPFormal.Analytic.CpNativeCarryRealOperatorZero

/-!
# Compatibility import: native real-operator zeros

This historical import path is retained so downstream files continue to
compile.  The former definition incorrectly conjoined quadratic mass
compatibility with boundary vanishing and therefore changed the meaning of
"zero".  The corrected API lives in
`CPFormal.Analytic.CpNativeCarryRealOperatorZero`:

* zero means boundary closure, at any radial coordinate;
* `sigma = 1 / 2` is the prior quadratic carry equilibrium;
* off-equilibrium obstruction belongs to the Green center/completed Green
  channel, not to the definition of zero.

No zero-confinement theorem is exported from this compatibility module.
-/
