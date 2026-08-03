import Mathlib.Tactic
import CPFormal.Analytic.CpFiniteGreenRadial
import CPFormal.Analytic.CpFiniteGreenPositivity
import CPFormal.Analytic.CpRadialCoercivity
import CPFormal.Analytic.CpGenuineCompatibility
import CPFormal.Analytic.CpGenuineQuotient

/-!
# Ponte de Green refletido: redução do boss a uma única seta

O fluxo de Green refletido factora exatamente (`CpFiniteGreenRadial`):

`finitePhaseNormalizedCpGreenFlux p M s = (p^(-δ) - p^δ) · E_M(s)`,

com `δ = criticalDisplacement s.re` e `E_M = finiteReflectedGradientPairing`.
A rigidez radial (`CpRadialCoercivity`) garante `p^(-δ) - p^δ = 0 ↔ δ = 0`.
Logo, se num zero Genuine esse fluxo de bulk se anula (**fechamento Green
forte** — a seta ainda aberta) e o pareamento é não nulo (**energia refletida**
— insumo do TFCD), então `Re(s) = 1/2`.

O fechamento do endpoint bracketado já provado no repositório não é a mesma
afirmação: no zero Genuine ele remove o bordo, deixando justamente este bulk
radial.  Portanto nenhum cancelamento de endpoint é usado aqui para fabricar a
anulação do fluxo.

Este módulo prova a **redução** (incondicional) e empacota a ponte num `structure`
cujos campos são exatamente esses dois insumos. Nenhuma instância é declarada.

Genuine First: nenhum zeta, equação funcional ou RH é usado.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-- **Redução núcleo.** Se o fluxo de Green refletido se anula e o pareamento é
não nulo, então `Re(s) = 1/2`. Puramente a rigidez radial + a fatoração exata. -/
theorem re_eq_half_of_flux_zero_of_pairing_ne
    (p : ℕ) (hp : Nat.Prime p) {s : ℂ} {M : ℕ}
    (hflux : finitePhaseNormalizedCpGreenFlux p M s = 0)
    (hpair : finiteReflectedGradientPairing M s ≠ 0) :
    s.re = 1 / 2 := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast hp.ne_one
  rw [finitePhaseNormalizedCpGreenFlux_eq_radialDifference_mul_pairing p M hp]
    at hflux
  rcases mul_eq_zero.mp hflux with hcoeff | hpz
  · have hreal :
        (p : ℝ) ^ (-criticalDisplacement s.re)
          - (p : ℝ) ^ criticalDisplacement s.re = 0 :=
      Complex.ofReal_eq_zero.mp hcoeff
    have hpow : (p : ℝ) ^ (-criticalDisplacement s.re)
        = (p : ℝ) ^ criticalDisplacement s.re := by linarith
    have hexp : -criticalDisplacement s.re = criticalDisplacement s.re :=
      (Real.rpow_right_inj hp0 hp1).mp hpow
    have hδ : criticalDisplacement s.re = 0 := by linarith
    have hre : s.re - 1 / 2 = 0 := by
      simpa [criticalDisplacement] using hδ
    linarith
  · exact absurd hpz hpair

/-- **Ponte de Green refletido.** Os dois insumos mínimos para localizar zeros
Genuine no eixo: a anulação forte do fluxo de bulk e a não-anulação da energia
refletida. -/
structure ReflectedGreenBridge (p M : ℕ) : Prop where
  flux_vanishes :
    ∀ {s : ℂ}, genuineContinuation s = 0 → s ∈ genuineCriticalStrip →
      finitePhaseNormalizedCpGreenFlux p M s = 0
  pairing_ne :
    ∀ {s : ℂ}, genuineContinuation s = 0 → s ∈ genuineCriticalStrip →
      finiteReflectedGradientPairing M s ≠ 0

/-- Dada a ponte, todo zero Genuine no strip tem parte real `1/2`. -/
theorem re_eq_half_of_reflectedGreenBridge
    (p : ℕ) (hp : Nat.Prime p) {M : ℕ} (bridge : ReflectedGreenBridge p M)
    {s : ℂ} (hzero : genuineContinuation s = 0)
    (hs : s ∈ genuineCriticalStrip) :
    s.re = 1 / 2 :=
  re_eq_half_of_flux_zero_of_pairing_ne p hp
    (bridge.flux_vanishes hzero hs) (bridge.pairing_ne hzero hs)

/-- **A energia refletida é não nula** em qualquer corte não vazio do strip —
descarregada pela positividade do TFCD (`finiteReflectedGradientPairing_re_pos`).
Parte real estritamente positiva, logo não nula. -/
theorem finiteReflectedGradientPairing_ne_zero
    {M : ℕ} (hM : 0 < M) {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    finiteReflectedGradientPairing M s ≠ 0 := by
  intro h
  have hpos := finiteReflectedGradientPairing_re_pos hM hs
  rw [h] at hpos
  simp at hpos

/-- **Coercividade quantitativa do detector Green.** No strip e em qualquer
corte refletido não vazio, a norma do fluxo domina linearmente o deslocamento
crítico.  A constante explícita é `2 * log p`, ponderada pela energia refletida
positiva. A estimativa é pontual: não afirma uma constante inferior uniforme
em `s` ou em `M`, pois o peso de energia depende de ambos. -/
theorem finitePhaseNormalizedCpGreenFlux_norm_ge_radialDefect
    (p M : ℕ) (hp : Nat.Prime p) (hM : 0 < M)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    2 * |criticalDisplacement s.re| * Real.log p *
        (finiteReflectedGradientPairing M s).re ≤
      ‖finitePhaseNormalizedCpGreenFlux p M s‖ := by
  have hradial :=
    abs_cpRadialDifference_ge p hp (criticalDisplacement s.re)
  have hpairPos := finiteReflectedGradientPairing_re_pos hM hs
  have hpairNorm :
      (finiteReflectedGradientPairing M s).re ≤
        ‖finiteReflectedGradientPairing M s‖ :=
    Complex.re_le_norm _
  have hcoefficientNorm :
      ‖(((p : ℝ) ^ (-criticalDisplacement s.re) -
          (p : ℝ) ^ criticalDisplacement s.re : ℝ) : ℂ)‖ =
        |cpRadialDifference p (criticalDisplacement s.re)| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    simpa [cpRadialDifference] using
      (abs_sub_comm
        ((p : ℝ) ^ (-criticalDisplacement s.re))
        ((p : ℝ) ^ criticalDisplacement s.re))
  calc
    2 * |criticalDisplacement s.re| * Real.log p *
          (finiteReflectedGradientPairing M s).re ≤
        |cpRadialDifference p (criticalDisplacement s.re)| *
          (finiteReflectedGradientPairing M s).re :=
      mul_le_mul_of_nonneg_right hradial hpairPos.le
    _ ≤ |cpRadialDifference p (criticalDisplacement s.re)| *
          ‖finiteReflectedGradientPairing M s‖ :=
      mul_le_mul_of_nonneg_left hpairNorm (abs_nonneg _)
    _ = ‖finitePhaseNormalizedCpGreenFlux p M s‖ := by
      rw [finitePhaseNormalizedCpGreenFlux_eq_radialDifference_mul_pairing
        p M hp s, norm_mul, hcoefficientNorm]

/-- **Detector radial exato.** Em qualquer corte refletido não vazio do strip,
o fluxo de bulk Green normalizado zera exatamente na meia-abscissa.  A direção
difícil usa a energia refletida estritamente positiva; a recíproca é a
substituição direta do deslocamento crítico nulo na fatoração radial. -/
theorem finitePhaseNormalizedCpGreenFlux_eq_zero_iff_re_eq_half
    (p M : ℕ) (hp : Nat.Prime p) (hM : 0 < M)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    finitePhaseNormalizedCpGreenFlux p M s = 0 ↔
      s.re = (1 : ℝ) / 2 := by
  constructor
  · intro hflux
    exact re_eq_half_of_flux_zero_of_pairing_ne p hp hflux
      (finiteReflectedGradientPairing_ne_zero hM hs)
  · intro hre
    rw [finitePhaseNormalizedCpGreenFlux_eq_radialDifference_mul_pairing
      p M hp s]
    simp [criticalDisplacement, hre]

/-- A única obrigação restante nesta rota, isolada como predicado: o fluxo de
bulk Green refletido se anula em todo zero Genuine no strip.  Isto é mais forte
que o cancelamento do endpoint já conhecido; pelos guards do projeto, é
equivalente à não-anulação forte.  Energia e rigidez radial já estão seladas. -/
def GreenFluxVanishesAtGenuineZeros (p M : ℕ) : Prop :=
  ∀ {s : ℂ}, genuineContinuation s = 0 → s ∈ genuineCriticalStrip →
    finitePhaseNormalizedCpGreenFlux p M s = 0

/-- **Boss reduzido a uma única seta.** Se o fluxo de bulk Green refletido se
anula em todo zero Genuine do strip, então todo zero Genuine tem parte real
`1/2`. A energia refletida está descarregada pelo TFCD; a rigidez radial faz o
resto. -/
theorem re_eq_half_of_greenFluxVanishes
    (p M : ℕ) (hp : Nat.Prime p) (hM : 0 < M)
    (hflux : GreenFluxVanishesAtGenuineZeros p M)
    {s : ℂ} (hzero : genuineContinuation s = 0)
    (hs : s ∈ genuineCriticalStrip) :
    s.re = 1 / 2 :=
  re_eq_half_of_flux_zero_of_pairing_ne p hp (hflux hzero hs)
    (finiteReflectedGradientPairing_ne_zero hM hs)

end

end CPFormal.Analytic.Cp
