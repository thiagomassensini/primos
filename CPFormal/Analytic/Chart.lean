import Mathlib

/-!
# Interface exata de uma carta

Uma instancia futura deve fornecer a identidade a partir das somas e dos
limites. Colocar a identidade como campo torna toda dependencia visivel; este
arquivo nao construi a carta CP por decreto.
-/

namespace CPFormal

structure ChartSpecification where
  genuine : ℂ → ℂ
  chart : ℂ → ℂ
  factor : ℂ → ℂ
  chart_identity : ∀ s : ℂ, chart s = factor s * genuine s

theorem ChartSpecification.chart_zero_iff_genuine_zero
    (spec : ChartSpecification) {s : ℂ} (hfactor : spec.factor s ≠ 0) :
    spec.chart s = 0 ↔ spec.genuine s = 0 := by
  rw [spec.chart_identity]
  simp [hfactor]

end CPFormal
