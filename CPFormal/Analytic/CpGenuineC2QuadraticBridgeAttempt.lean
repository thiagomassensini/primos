import CPFormal.Analytic.CpC2GpreGreenActivationGuard
import CPFormal.Analytic.CpConnectedC2Defect

/-!
# Direct quadratic C2 probe for a raw Genuine zero

This file deliberately asks the Lean kernel to compose the strongest already
proved scalar C2/Gpre closure with the positive radial C2 detector.

No bridge hypothesis, axiom, `sorry`, or copy of the conclusion is supplied.
The expected diagnostic is the exact residual obligation left after the
tagged scalar synthesis has been closed at a Genuine zero.
-/

open scoped Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/--
Direct kernel probe:

`raw Genuine zero -> tagged C2/Gpre scalar closure
                  -> radial connected C2 detector closure`.

The first arrow is already a theorem.  This probe asks Lean to synthesize the
second arrow from the present library.
-/
theorem genuine_zero_to_radialC2Detector_zero_probe
    (verticalRatio : ℝ) {p q : ℕ}
    (family : C2GpreActiveCofinalAtlasFamily p q)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    crossPrimeRadialC2Detector p q
      (criticalDisplacement s.re) = 0 := by
  have hscalar :
      Tendsto
        (fun L : ℕ =>
          c2GpreNormalizedCofinalTaggedSynthesis
            verticalRatio family L s)
        atTop (nhds 0) :=
    c2GpreNormalizedCofinalTaggedSynthesis_tendsto_zero_of_genuine_zero
      verticalRatio family hp hpodd hq hqodd hs hzero
  aesop

end

end CPFormal.Analytic.Cp
