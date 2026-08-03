import CPFormal.Analytic.CpGenuineFirstTermDominanceNonempty
import CPFormal.Analytic.CpReflectedGreenBridge

/-!
# Capstone: os dois canais vivos num ponto off-critical concreto

Reúne o minorante incondicional (canal escalar) com o detector radial exato
(canal Green) num único ponto off-critical explícito.

Na região de dominância do primeiro termo não há zero Genuine algum
(`genuineContinuation_ne_zero_on_firstTermDominanceRegion`).  Pelo detector exato
`finitePhaseNormalizedCpGreenFlux_eq_zero_iff_re_eq_half`, fora da linha crítica o
fluxo de Green refletido também é não nulo.  Logo, no ponto concreto `s = 4/5`,
**ambos** os canais do operador completado estão vivos:

* escalar:   `genuineContinuation s ≠ 0`   (novo — pelo minorante coercivo);
* radial:    `finitePhaseNormalizedCpGreenFlux p M s ≠ 0`   (pelo detector).

Esta é a realização concreta, num ponto explícito, da leitura do operador
completado: off-critical, nenhum dos dois canais colapsa.

Genuine First: nenhum zeta, equação funcional ou RH.
-/

namespace CPFormal.Analytic.Cp

/-- Fora da linha crítica, na região de dominância, o fluxo de Green refletido é
não nulo (detector radial exato). -/
theorem greenFlux_ne_zero_on_firstTermDominanceRegion_offCritical
    (p M : ℕ) (hp : Nat.Prime p) (hM : 0 < M)
    {s : ℂ} (hs : s ∈ firstTermDominanceRegion) (hoff : s.re ≠ 1 / 2) :
    finitePhaseNormalizedCpGreenFlux p M s ≠ 0 := by
  intro h
  exact hoff
    ((finitePhaseNormalizedCpGreenFlux_eq_zero_iff_re_eq_half p M hp hM hs.1).1 h)

/-- **Capstone.**  Existe um ponto off-critical concreto no strip onde tanto o
canal escalar Genuine quanto o fluxo de Green refletido são não nulos: ambos os
canais do operador completado estão vivos fora da linha crítica. -/
theorem exists_offCritical_bothChannels_ne_zero
    (p M : ℕ) (hp : Nat.Prime p) (hM : 0 < M) :
    ∃ s : ℂ, s ∈ genuineCriticalStrip ∧ s.re ≠ 1 / 2 ∧
      genuineContinuation s ≠ 0 ∧
      finitePhaseNormalizedCpGreenFlux p M s ≠ 0 := by
  obtain ⟨s, hs, hoff⟩ := firstTermDominanceRegion_nonempty
  exact ⟨s, hs.1, hoff,
    genuineContinuation_ne_zero_on_firstTermDominanceRegion hs,
    greenFlux_ne_zero_on_firstTermDominanceRegion_offCritical p M hp hM hs hoff⟩

/-- **Confinamento numa região concreta não-vazia.**  A região de dominância do
primeiro termo é não-vazia, contém um ponto off-critical, e nela todo zero Genuine
está em `Re(s)=1/2` (realizado por ausência de zeros).  O pipeline
minorante → confinamento é instanciado sem hipótese. -/
theorem exists_nonempty_offCritical_confinedRegion :
    ∃ s : ℂ, s ∈ firstTermDominanceRegion ∧ s.re ≠ 1 / 2 ∧
      (∀ ⦃z : ℂ⦄, z ∈ firstTermDominanceRegion → genuineContinuation z = 0 →
        z.re = 1 / 2) := by
  obtain ⟨s, hs, hoff⟩ := firstTermDominanceRegion_nonempty
  exact ⟨s, hs, hoff, genuineConfined_on_firstTermDominanceRegion⟩

end CPFormal.Analytic.Cp
