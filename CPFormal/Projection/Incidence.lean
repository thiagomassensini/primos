import Mathlib

/-!
# Sintese e incidencia de posto um

Esta camada e deliberadamente algebrica. A continuidade, o vetor de Riesz e a
autoadjunticidade da projecao ponderada entram numa etapa posterior.
-/

namespace CPFormal

variable {E : Type*} [AddCommMonoid E] [Module ℂ E]

/-- Mapa de posto um produzido por um funcional, uma direcao e um normalizador. -/
def algebraicRankOne
    (synthesis : E →ₗ[ℂ] ℂ) (direction : E) (normalizer : ℂ)
    (z : E) : E :=
  (synthesis z / normalizer) • direction

theorem algebraicRankOne_eq_zero_of_synthesis_eq_zero
    (synthesis : E →ₗ[ℂ] ℂ) (direction : E) (normalizer : ℂ)
    {z : E} (hz : synthesis z = 0) :
    algebraicRankOne synthesis direction normalizer z = 0 := by
  simp [algebraicRankOne, hz]

end CPFormal
