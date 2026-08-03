import CPFormal.Analytic.CpReflectedGreenBridge
import CPFormal.Analytic.CpPairedGenuineBridgeTarget

/-!
# A ponte de confinamento: as duas frentes são a mesma afirmação

Este módulo prova que as duas rotas de ataque à fronteira — o **detector Green
refletido** (`GreenFluxVanishesAtGenuineZeros`) e o **piso escalar coercivo** da
rota book-cash (não-anulação do alvo pareado `genuineCentralContinuationC2`) — não
são estratégias concorrentes: são **reformulações equivalentes** do mesmo
confinamento.

O elo lógico é limpo e não usa dominância:

* o detector Green é **exato** (`finitePhaseNormalizedCpGreenFlux_eq_zero_iff_re_eq_half`):
  fluxo zera ⟺ `Re(s)=1/2`.  Logo, `GreenFluxVanishesAtGenuineZeros` equivale a
  confinar todo zero Genuine na linha crítica (canal radial, ortogonal);
* o adaptador `genuineCentralContinuationC2_eq_zero_iff` mostra que o alvo
  book-cash e o Genuine canônico têm exatamente os mesmos zeros no strip (canal
  escalar).  Logo, o piso escalar off-critical equivale ao piso do alvo pareado.

Reunindo tudo, as quatro condições abaixo são equivalentes.  Provar **qualquer
uma** fecha as outras três.  Este arquivo NÃO prova nenhuma delas — a fronteira
permanece aberta e honesta; ele apenas identifica que Green e book-cash são a
mesma seta.

Genuine First: nenhum zeta, equação funcional ou RH.
-/

namespace CPFormal.Analytic.Cp

/-- **Alvo neutro.** Todo zero Genuine no strip está na linha crítica. -/
def GenuineConfinedInStrip : Prop :=
  ∀ ⦃s : ℂ⦄, s ∈ genuineCriticalStrip → genuineContinuation s = 0 → s.re = 1 / 2

/-- **Piso escalar.** O Genuine canônico não se anula fora da linha crítica no
strip. -/
def GenuineNonvanishingOffCritical : Prop :=
  ∀ ⦃s : ℂ⦄, s ∈ genuineCriticalStrip → s.re ≠ 1 / 2 → genuineContinuation s ≠ 0

/-- **Piso book-cash.** O alvo pareado coercivo não se anula fora da linha
crítica no strip. -/
def CentralNonvanishingOffCritical : Prop :=
  ∀ ⦃s : ℂ⦄, s ∈ genuineCriticalStrip → s.re ≠ 1 / 2 →
    genuineCentralContinuationC2 s ≠ 0

/-- Confinamento ⟺ piso escalar (pura contraposição). -/
theorem genuineConfinedInStrip_iff_nonvanishingOffCritical :
    GenuineConfinedInStrip ↔ GenuineNonvanishingOffCritical := by
  constructor
  · intro h s hs hoff hzero
    exact hoff (h hs hzero)
  · intro h s hs hzero
    by_contra hne
    exact h hs hne hzero

/-- Piso escalar ⟺ piso book-cash (adaptador de fator nunca nulo). -/
theorem nonvanishingOffCritical_iff_centralNonvanishing :
    GenuineNonvanishingOffCritical ↔ CentralNonvanishingOffCritical := by
  constructor
  · intro h s hs hoff hC
    exact h hs hoff ((genuineCentralContinuationC2_eq_zero_iff hs).1 hC)
  · intro h s hs hoff hz
    exact h hs hoff ((genuineCentralContinuationC2_eq_zero_iff hs).2 hz)

/-- **Ponte Green.** A fronteira do fluxo Green refletido equivale ao
confinamento — via o detector radial exato, sem dominância. -/
theorem greenFluxVanishesAtGenuineZeros_iff_confined
    (p M : ℕ) (hp : Nat.Prime p) (hM : 0 < M) :
    GreenFluxVanishesAtGenuineZeros p M ↔ GenuineConfinedInStrip := by
  constructor
  · intro hflux s hs hzero
    exact re_eq_half_of_greenFluxVanishes p M hp hM hflux hzero hs
  · intro hconf s hzero hs
    exact (finitePhaseNormalizedCpGreenFlux_eq_zero_iff_re_eq_half p M hp hM hs).2
      (hconf hs hzero)

/-- **Equivalência-mestre.** O detector Green refletido e o piso escalar
book-cash são a mesma afirmação: ambos equivalem ao confinamento. Provar uma
frente fecha a outra. -/
theorem greenFluxVanishes_iff_centralNonvanishing
    (p M : ℕ) (hp : Nat.Prime p) (hM : 0 < M) :
    GreenFluxVanishesAtGenuineZeros p M ↔ CentralNonvanishingOffCritical :=
  (greenFluxVanishesAtGenuineZeros_iff_confined p M hp hM).trans
    (genuineConfinedInStrip_iff_nonvanishingOffCritical.trans
      nonvanishingOffCritical_iff_centralNonvanishing)

/-- Forma escalar da mesma ponte: fluxo Green ⟺ piso escalar canônico. -/
theorem greenFluxVanishes_iff_nonvanishingOffCritical
    (p M : ℕ) (hp : Nat.Prime p) (hM : 0 < M) :
    GreenFluxVanishesAtGenuineZeros p M ↔ GenuineNonvanishingOffCritical :=
  (greenFluxVanishesAtGenuineZeros_iff_confined p M hp hM).trans
    genuineConfinedInStrip_iff_nonvanishingOffCritical

end CPFormal.Analytic.Cp
