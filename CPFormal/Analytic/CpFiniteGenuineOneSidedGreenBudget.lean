import CPFormal.Analytic.CpFiniteGenuineAngularGreenBudget

/-!
# Orcamento Green unilateral a partir de um unico zero Genuine

O checkpoint 0.38 usou um par de zeros `s` e `s#` para fazer desaparecer o
produto das duas portas angulares. Essa hipotese e desnecessaria. Num zero
Genuine, a primeira porta tende a zero. A porta refletida nao precisa zerar:
como `s#` permanece no strip, ela converge para o valor finito da carta
bracketada em `s#`. Portanto

`conj(Phi_M(s)) * Phi_M(s#) -> 0`.

Este arquivo remove completamente a estabilidade refletida de zeros da ponte
do 0.38. A unica obrigacao restante e o fechamento, depois do peso radial, da
correcao angular local mais off-diagonal. Nenhuma zeta, equacao funcional ou
simetria de zeros e usada.
-/

open scoped BigOperators Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-!
## A segunda porta precisa somente convergir
-/

/-- A porta no parametro refletido converge em todo o strip, sem hipotese de
zero em `s#`. -/
theorem finiteCanonicalAngularTrace_reflected_tendsto
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ ↦
        finiteCanonicalAngularTrace M (reflectedParameter s))
      atTop
      (nhds (bracketedDirichletChart 3 (reflectedParameter s))) := by
  have hsSharp := reflectedParameter_mem_genuineCriticalStrip hs
  exact finiteCanonicalAngularTrace_tendsto hsSharp.1

/-- Um unico zero Genuine anula o produto refletido das portas. -/
theorem finiteCanonicalAngularScalarPairing_tendsto_zero_of_genuine_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto (fun M : ℕ ↦ finiteCanonicalAngularScalarPairing M s)
      atTop (nhds 0) := by
  have hphi :=
    finiteCanonicalAngularTrace_tendsto_zero_of_genuine_zero hs hzero
  have hphiSharp := finiteCanonicalAngularTrace_reflected_tendsto hs
  have hconj :
      Tendsto
        (fun M : ℕ ↦
          (starRingEnd ℂ) (finiteCanonicalAngularTrace M s))
        atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (Complex.continuous_conj.tendsto 0).comp hphi
  have hproduct := hconj.mul hphiSharp
  simpa only [finiteCanonicalAngularScalarPairing_eq_product,
    zero_mul] using hproduct

/-- O orcamento Green inteiro tende a zero a partir apenas do zero em `s`. -/
theorem finiteCanonicalAngularGreenBudget_tendsto_zero_of_genuine_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
      (fun M : ℕ ↦
        finiteReflectedGradientPairing (3 * M) s +
          finiteCanonicalAngularGreenCorrection M s)
      atTop (nhds 0) := by
  simpa only [← finiteCanonicalAngularScalarPairing_eq_green_add_correction]
    using
      finiteCanonicalAngularScalarPairing_tendsto_zero_of_genuine_zero
        hs hzero

/-!
## Unica obrigacao restante
-/

/--
Interface Genuine-first minima: somente a correcao angular nao radial precisa
fechar depois do coeficiente radial. Nao ha campo de zero refletido.
-/
structure GenuineOneSidedAngularGreenBridge (p : ℕ) : Prop where
  scaled_correction_closes :
    ∀ {s : ℂ}, genuineContinuation s = 0 →
      s ∈ genuineCriticalStrip →
      Tendsto
        (fun M : ℕ ↦
          ((cpRadialDifference p (criticalDisplacement s.re) : ℝ) : ℂ) *
            finiteCanonicalAngularGreenCorrection M s)
        atTop (nhds 0)

/-!
O teorema local abaixo deixa a dependencia inteira visivel: zero Genuine,
strip e fechamento da correcao. A positividade Green faz o resto.
-/
theorem criticalDisplacement_eq_zero_of_genuine_zero_of_scaled_correction
    {p : ℕ} (hp : Nat.Prime p)
    {s : ℂ} (hzero : genuineContinuation s = 0)
    (hs : s ∈ genuineCriticalStrip)
    (hcorrection :
      Tendsto
        (fun M : ℕ ↦
          ((cpRadialDifference p (criticalDisplacement s.re) : ℝ) : ℂ) *
            finiteCanonicalAngularGreenCorrection M s)
        atTop (nhds 0)) :
    criticalDisplacement s.re = 0 := by
  let c : ℝ := cpRadialDifference p (criticalDisplacement s.re)
  have hbudget :=
    finiteCanonicalAngularGreenBudget_tendsto_zero_of_genuine_zero hs hzero
  have hscaledBudget :
      Tendsto
        (fun M : ℕ ↦
          (c : ℂ) *
            (finiteReflectedGradientPairing (3 * M) s +
              finiteCanonicalAngularGreenCorrection M s))
        atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hbudget
  have hcorrection' :
      Tendsto
        (fun M : ℕ ↦
          (c : ℂ) * finiteCanonicalAngularGreenCorrection M s)
        atTop (nhds 0) := by
    simpa [c] using hcorrection
  have hpairingComplex :
      Tendsto
        (fun M : ℕ ↦
          (c : ℂ) * finiteReflectedGradientPairing (3 * M) s)
        atTop (nhds 0) := by
    have hsub := hscaledBudget.sub hcorrection'
    have hfun :
        (fun M : ℕ ↦
          (c : ℂ) * finiteReflectedGradientPairing (3 * M) s) =
        (fun M : ℕ ↦
          (c : ℂ) *
              (finiteReflectedGradientPairing (3 * M) s +
                finiteCanonicalAngularGreenCorrection M s) -
            (c : ℂ) * finiteCanonicalAngularGreenCorrection M s) := by
      funext M
      ring
    rw [hfun]
    simpa using hsub
  have hpairingReal :
      Tendsto
        (fun M : ℕ ↦
          c * (finiteReflectedGradientPairing (3 * M) s).re)
        atTop (nhds 0) := by
    have hre :=
      Complex.continuous_re.continuousAt.tendsto.comp hpairingComplex
    simpa [Function.comp_def, Complex.mul_re] using hre
  have hpositive :
      0 < (finiteReflectedGradientPairing 1 s).re :=
    finiteReflectedGradientPairing_re_pos (by norm_num) hs
  have hmonotone := finiteReflectedGradientPairing_re_monotone hs
  have hbound :
      ∀ᶠ M in atTop,
        (finiteReflectedGradientPairing 1 s).re ≤
          (finiteReflectedGradientPairing (3 * M) s).re :=
    eventually_atTop.2 ⟨1, fun M hM ↦ hmonotone (by omega)⟩
  have hc : c = 0 :=
    constant_eq_zero_of_tendsto_mul_of_eventually_pos_lower_bound
      hpositive hbound hpairingReal
  dsimp [c] at hc
  exact (cpRadialDifference_eq_zero_iff
    p hp (criticalDisplacement s.re)).mp hc

/-- A interface unilateral fecha o tilt em todo zero Genuine do strip. -/
theorem GenuineOneSidedAngularGreenBridge.criticalDisplacement_eq_zero
    {p : ℕ} (hp : Nat.Prime p)
    (bridge : GenuineOneSidedAngularGreenBridge p)
    {s : ℂ} (hzero : genuineContinuation s = 0)
    (hs : s ∈ genuineCriticalStrip) :
    criticalDisplacement s.re = 0 :=
  criticalDisplacement_eq_zero_of_genuine_zero_of_scaled_correction
    hp hzero hs (bridge.scaled_correction_closes hzero hs)

/-- A ponte antiga do 0.38 possui mais dados que a interface realmente usa. -/
theorem GenuineAngularGreenCancellationBridge.toOneSidedBridge
    {p : ℕ} (bridge : GenuineAngularGreenCancellationBridge p) :
    GenuineOneSidedAngularGreenBridge p := by
  refine ⟨?_⟩
  intro s hzero hs
  exact bridge.scaled_correction_closes hzero hs

/-- A unica obrigacao restante constroi a ponte carry--Green do 0.37. -/
theorem GenuineOneSidedAngularGreenBridge.toGenuineCarryFluxBridge
    {p : ℕ} (hp : Nat.Prime p)
    (bridge : GenuineOneSidedAngularGreenBridge p) :
    GenuineCarryFluxBridge p := by
  refine ⟨?_⟩
  intro s hzero hs
  have hcritical := bridge.criticalDisplacement_eq_zero hp hzero hs
  exact finiteBracketCoupledCpGreenFlux_tendsto_zero_of_critical
    p hp hs hzero hcritical

end

end CPFormal.Analytic.Cp
