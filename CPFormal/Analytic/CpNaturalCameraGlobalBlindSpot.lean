import CPFormal.Analytic.CpNaturalCameraAnalyticContinuation
import CPFormal.Analytic.CpGenuineFirstOrthogonalGreenLimit

/-!
# Global natural-camera blind points and retained Green energy

The native camera algebra is not prime-specific. Every nondegenerate natural
width `b >= 3` factors through the same `genuineContinuation` on the critical
strip. This module packages the resulting universal quantifier: a Genuine
zero is a simultaneous blind point of every such camera, and every finite
native camera resultant converges to zero there.

At the same parameter, the reflected Green energy is still strictly positive.
This proves that disappearance from all scalar camera readouts is not the same
statement as disappearance of the Green energy. It does **not** identify that
Green energy with one common pre-compression state for all natural cameras;
that stronger identification remains the separately typed
`GREEN-NATCAM-INTERTWINER` frontier.

The literal native width `2` is degenerate. The nondegenerate aligned `C2`
scanner has one leg on each side and is encoded by the native width parameter
`4`, whose `halfRange` is still `1`; this is not an identification with a
four-leg geometric `C4` camera.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-- A parameter invisible to every nondegenerate natural camera at once. -/
def IsNaturalCameraGlobalBlindPoint (s : ℂ) : Prop :=
  ∀ b : ℕ, 3 ≤ b → bracketedDirichletChart b s = 0

/-- On the critical strip, the common scalar Genuine zero is exactly the
simultaneous blind point of all nondegenerate natural cameras. -/
theorem genuineContinuation_zero_iff_naturalCameraGlobalBlindPoint
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    genuineContinuation s = 0 ↔ IsNaturalCameraGlobalBlindPoint s := by
  constructor
  · intro hzero b hb
    rw [bracketedDirichletChart_eq_naturalCameraFactor_mul_genuineContinuation
      b hb hs, hzero, mul_zero]
  · intro hblind
    exact
      (bracketedDirichletChart_zero_iff_genuineContinuation_zero
        3 (by norm_num) (by norm_num) hs).1
        (hblind 3 (by norm_num))

/-- At a Genuine zero, every finite natural-camera sequence converges to the
zero resultant, without a primality or parity hypothesis. -/
theorem naturalCameraFiniteResultants_tendsto_zero_of_genuine_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    ∀ b : ℕ, ∀ _hb : 3 ≤ b,
      Filter.Tendsto
        (fun M : ℕ ↦
          nativeCarryFiniteSaturatedChart b M (dirichletTerm s))
        Filter.atTop (nhds 0) := by
  intro b hb
  simpa [hzero] using
    (nativeCarryFiniteSaturatedChart_dirichlet_tendsto_factor_mul_genuineContinuation
      b hb hs)

/-- A raw Genuine zero is simultaneously invisible to every natural camera
while the independently constructed reflected Green energy remains positive.

This conjunction is deliberately weaker than a common state-level
intertwiner between all natural-camera energies and the Green carrier. -/
theorem genuineZero_globalNaturalCameraBlind_and_greenEnergy_pos
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    IsNaturalCameraGlobalBlindPoint s ∧
      0 < infiniteReflectedGreenEnergy s := by
  exact ⟨
    (genuineContinuation_zero_iff_naturalCameraGlobalBlindPoint hs).1 hzero,
    infiniteReflectedGreenEnergy_pos hs⟩

end

end CPFormal.Analytic.Cp
