import CPFormal.Analytic.CpGenuineOffCriticalWitnessCapstone
import CPFormal.Analytic.CpGenuineGreenCompletedOperator

/-!
# "Dois canais vivos" como propriedade da região inteira

Generaliza a testemunha pontual: em **todo** ponto off-critical da região de
dominância do primeiro termo, ambos os canais do operador completado são não
nulos.  O mecanismo não depende do ponto específico — é uma propriedade da
região.

* escalar: `genuineContinuation s ≠ 0`  (minorante coercivo);
* radial:  `finitePhaseNormalizedCpGreenFlux p M s ≠ 0`  (detector exato);
* completado: `genuineGreenCompletedLimitOperator p q s ≠ 0`  (ambos os conjuntos
  do kernel falham).

Genuine First: nenhum zeta, equação funcional ou RH.
-/

namespace CPFormal.Analytic.Cp

/-- **Dois canais vivos, regional.**  Em todo ponto off-critical da região, o canal
escalar Genuine e o fluxo de Green refletido são simultaneamente não nulos. -/
theorem bothChannels_ne_zero_on_region
    (p M : ℕ) (hp : Nat.Prime p) (hM : 0 < M)
    {s : ℂ} (hs : s ∈ firstTermDominanceRegion) (hoff : s.re ≠ 1 / 2) :
    genuineContinuation s ≠ 0 ∧ finitePhaseNormalizedCpGreenFlux p M s ≠ 0 :=
  ⟨genuineContinuation_ne_zero_on_firstTermDominanceRegion hs,
    greenFlux_ne_zero_on_firstTermDominanceRegion_offCritical p M hp hM hs hoff⟩

/-- **Operador completado não nulo, regional.**  Em todo ponto da região o canal
escalar Genuine é não nulo, o que já faz o primeiro conjunto do kernel do operador
completado falhar; logo o operador é não nulo em toda a região. -/
theorem completed_ne_zero_on_region
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    {s : ℂ} (hs : s ∈ firstTermDominanceRegion) :
    genuineGreenCompletedLimitOperator p q s ≠ 0 := by
  intro hcomp
  exact genuineContinuation_ne_zero_on_firstTermDominanceRegion hs
    ((genuineGreenCompletedLimitOperator_eq_zero_iff p q hp hq hs.1).1 hcomp).1

end CPFormal.Analytic.Cp
