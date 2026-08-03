import CPFormal.Analytic.CpGenuineFirstTermDominanceNonempty
import CPFormal.Analytic.CpGenuineGreenCompletedOperator

/-!
# Testemunha do operador completado: ambos os conjuntos do kernel falham

O operador completado Genuine–Green tem kernel exatamente
`genuineGreenCompletedLimitOperator p q s = 0 ↔
  genuineContinuation s = 0 ∧ criticalDisplacement s.re = 0`
(`genuineGreenCompletedLimitOperator_eq_zero_iff`).

Fora da linha crítica o segundo conjunto já falha (`δ ≠ 0`).  Com o minorante
coercivo, agora o **primeiro** conjunto também falha num ponto explícito
(`genuineContinuation s ≠ 0`).  Portanto, no ponto off-critical concreto, o
operador completado é não nulo por **ambas** as razões independentes — a
realização literal, num ponto, da leitura em soma direta.

Genuine First: nenhum zeta, equação funcional ou RH.
-/

namespace CPFormal.Analytic.Cp

/-- **Testemunha completa.**  Existe um ponto off-critical no strip onde o canal
escalar Genuine é não nulo e, por consequência, o operador completado é não nulo
(os dois conjuntos do seu kernel falham simultaneamente). -/
theorem exists_offCritical_completed_and_scalar_ne_zero
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    ∃ s : ℂ, s ∈ genuineCriticalStrip ∧ s.re ≠ 1 / 2 ∧
      genuineContinuation s ≠ 0 ∧
      genuineGreenCompletedLimitOperator p q s ≠ 0 := by
  obtain ⟨s, hs, hoff, hscalar⟩ := exists_offCritical_genuineContinuation_ne_zero
  refine ⟨s, hs, hoff, hscalar, ?_⟩
  intro hcomp
  exact hscalar
    ((genuineGreenCompletedLimitOperator_eq_zero_iff p q hp hq hs).1 hcomp).1

end CPFormal.Analytic.Cp
