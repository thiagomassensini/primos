import CPFormal.Analytic.CpGenuineConfinementBridge
import CPFormal.Analytic.CpPairedBookCoercivity
import CPFormal.Analytic.CpReflectedGreenBridge

/-!
# Confinamento regional: o receptor do minorante coercivo

O repositório `formalizacao_C2` formaliza o **minorante** da rota book-cash como
um motor abstrato (`regionalVerticalQuartetBulk_nonvanishing`,
`regionalVerticalBulk_nonvanishing_of_bounds`): dado, numa região off-critical,
um dado de dominância `‖E‖ < ‖K‖` (com o piso do quarteto `(1-r)(1+r²)` ou o
piso sharp do resolvente `1/(1+r)`), conclui-se que o alvo pareado não se anula.

Este módulo é o **receptor nativo** desse minorante no `primos`.  Ele fecha o
pipeline:

```text
dado de dominância regional            (insumo: o minorante do formalizacao_C2)
  ──(no_zero_of_dominance)──▶  genuineCentralContinuationC2 ≠ 0 na região
  ──(adaptador de zeros)────▶  genuineContinuation ≠ 0 off-critical na região
  ──(contraposição)─────────▶  confinamento regional (zero Genuine ⟹ Re=1/2)
  ──(detector Green exato)──▶  fluxo Green refletido zera nos zeros da região
```

Nenhuma dominância é fabricada aqui: o dado de dominância entra como hipótese
explícita — é exatamente o que os certificados regionais do `formalizacao_C2`
fornecem.  O que este módulo prova é a **transferência** limpa desse insumo até o
confinamento e o fluxo Green.

Genuine First: nenhum zeta, equação funcional ou RH.
-/

namespace CPFormal.Analytic.Cp

/-- **Não-anulação regional do alvo central a partir de dominância.**  Numa região
onde o alvo pareado se decompõe como `K + E` com `E` estritamente dominado por
`K`, o alvo não se anula.  Este é o receptor direto do minorante coercivo. -/
theorem central_nonvanishing_on_of_dominance
    {R : Set ℂ} {K E : ℂ → ℂ} {L Rb : ℂ → ℝ}
    (hdecomp : ∀ ⦃s⦄, s ∈ R → genuineCentralContinuationC2 s = K s + E s)
    (hK : ∀ ⦃s⦄, s ∈ R → L s ≤ ‖K s‖)
    (hE : ∀ ⦃s⦄, s ∈ R → ‖E s‖ ≤ Rb s)
    (hdom : ∀ ⦃s⦄, s ∈ R → Rb s < L s) :
    ∀ ⦃s⦄, s ∈ R → genuineCentralContinuationC2 s ≠ 0 := fun _ hsR =>
  no_zero_of_dominance (hdecomp hsR) (hK hsR) (hE hsR) (hdom hsR)

/-- **Confinamento regional a partir da não-anulação central.**  Se o alvo pareado
não se anula fora da linha crítica numa região do strip, então todo zero Genuine
dessa região está em `Re(s)=1/2`. -/
theorem genuineConfined_on_of_central_nonvanishing
    {R : Set ℂ} (hRstrip : R ⊆ genuineCriticalStrip)
    (hnv : ∀ ⦃s⦄, s ∈ R → s.re ≠ 1 / 2 → genuineCentralContinuationC2 s ≠ 0) :
    ∀ ⦃s⦄, s ∈ R → genuineContinuation s = 0 → s.re = 1 / 2 := by
  intro s hsR hzero
  by_contra hoff
  exact hnv hsR hoff ((genuineCentralContinuationC2_eq_zero_iff (hRstrip hsR)).2 hzero)

/-- **Pipeline completo: dominância regional ⟹ confinamento regional.**  Reúne o
receptor do minorante e a contraposição.  A entrada é exatamente o dado de
dominância que os certificados do `formalizacao_C2` provam em cada caixa/disco. -/
theorem genuineConfined_on_of_regional_dominance
    {R : Set ℂ} {K E : ℂ → ℂ} {L Rb : ℂ → ℝ}
    (hRstrip : R ⊆ genuineCriticalStrip)
    (hdecomp : ∀ ⦃s⦄, s ∈ R → genuineCentralContinuationC2 s = K s + E s)
    (hK : ∀ ⦃s⦄, s ∈ R → L s ≤ ‖K s‖)
    (hE : ∀ ⦃s⦄, s ∈ R → ‖E s‖ ≤ Rb s)
    (hdom : ∀ ⦃s⦄, s ∈ R → Rb s < L s) :
    ∀ ⦃s⦄, s ∈ R → genuineContinuation s = 0 → s.re = 1 / 2 :=
  genuineConfined_on_of_central_nonvanishing hRstrip
    (fun {_} hsR _ => central_nonvanishing_on_of_dominance hdecomp hK hE hdom hsR)

/-- **Fecho Green regional.**  Na mesma região, o minorante coercivo força o fluxo
de Green refletido a se anular em todo zero Genuine — via o detector radial exato,
sem dominância no lado Green. -/
theorem greenFluxVanishes_on_of_regional_dominance
    (p M : ℕ) (hp : Nat.Prime p) (hM : 0 < M)
    {R : Set ℂ} {K E : ℂ → ℂ} {L Rb : ℂ → ℝ}
    (hRstrip : R ⊆ genuineCriticalStrip)
    (hdecomp : ∀ ⦃s⦄, s ∈ R → genuineCentralContinuationC2 s = K s + E s)
    (hK : ∀ ⦃s⦄, s ∈ R → L s ≤ ‖K s‖)
    (hE : ∀ ⦃s⦄, s ∈ R → ‖E s‖ ≤ Rb s)
    (hdom : ∀ ⦃s⦄, s ∈ R → Rb s < L s) :
    ∀ ⦃s⦄, s ∈ R → genuineContinuation s = 0 →
      finitePhaseNormalizedCpGreenFlux p M s = 0 := by
  intro s hsR hzero
  have hre : s.re = 1 / 2 :=
    genuineConfined_on_of_regional_dominance hRstrip hdecomp hK hE hdom hsR hzero
  exact (finitePhaseNormalizedCpGreenFlux_eq_zero_iff_re_eq_half p M hp hM
    (hRstrip hsR)).2 hre

end CPFormal.Analytic.Cp
