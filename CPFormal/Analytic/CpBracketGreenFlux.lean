import CPFormal.Analytic.CpBracketGreenBoundary

/-!
# Fluxo Green acoplado: reducao exata do proximo gargalo

Depois do fechamento do bordo bracketado, resta decidir se o fluxo acoplado
se anula nos zeros do Genuine. Este arquivo nao postula essa anulacao.

Primeiro separamos novamente as duas parcelas independentes:

`coupledFlux = Re(orientedBulkFlux) + coupledBoundary`.

Em seguida usamos a positividade termo a termo para mostrar que a parte real
do pareamento refletido e monotona e fica uniformemente afastada de zero a
partir do primeiro corte. Como consequencia, num zero Genuine, o fluxo
acoplado converge a zero se, e somente se, `Re(s)=1/2`.

Portanto a anulacao desse fluxo nao e um detalhe tecnico que possa ser obtido
da propria identidade Green: ela e exatamente a ponte critica ainda aberta.
-/

open scoped BigOperators Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-- Adicionar uma aresta adiciona exatamente seu somador ao pareamento. -/
theorem finiteReflectedGradientPairing_succ (M : ℕ) (s : ℂ) :
    finiteReflectedGradientPairing (M + 1) s =
      finiteReflectedGradientPairing M s +
        finiteReflectedGradientEdge M s := by
  unfold finiteReflectedGradientPairing finiteReflectedGradientEdge
  rw [Finset.sum_range_succ]

/-- As partes reais dos pareamentos finitos crescem com o corte. -/
theorem finiteReflectedGradientPairing_re_monotone
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Monotone (fun M : ℕ ↦ (finiteReflectedGradientPairing M s).re) := by
  apply monotone_nat_of_le_succ
  intro M
  rw [finiteReflectedGradientPairing_succ]
  simp only [Complex.add_re]
  exact le_add_of_nonneg_right
    (le_of_lt (finiteReflectedGradientEdge_re_pos hs M))

/-!
Forma nao comprimida do fluxo acoplado. O traco bracketado modifica apenas a
corrente de Stokes/bordo; a parcela de bulk orientada continua visivel.
-/
theorem finiteBracketCoupledCpGreenFlux_eq_oriented_add_boundary
    (p M : ℕ) (s : ℂ) :
    finiteBracketCoupledCpGreenFlux p M s =
      (finiteOrientedCpGreenFlux p M s).re +
        finiteBracketCoupledSignedBoundary M s := by
  unfold finiteBracketCoupledCpGreenFlux finiteSignedCpGreenFlux
    finiteBracketCoupledSignedBoundary finiteSignedCpGreenBoundary
  rw [finiteReflectedStokesFlux_eq_endpoints]
  unfold finiteReflectedBoundary
  ring

/-- O bulk acoplado conserva a fatoracao radial exata. -/
theorem finiteBracketCoupledCpGreenFlux_eq_radialDifference_mul_pairing
    (p M : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    finiteBracketCoupledCpGreenFlux p M s =
      cpRadialDifference p (criticalDisplacement s.re) *
          (finiteReflectedGradientPairing M s).re +
        finiteBracketCoupledSignedBoundary M s := by
  rw [finiteBracketCoupledCpGreen_identity p M hp s]
  unfold finiteRadialGreenEnergy
  rw [cpRadialDifference_eq_two_mul_delta_mul_cofactor]
  ring

/-!
Lema topologico elementar: um multiplo constante de uma sequencia que fica
acima de uma constante positiva nao pode convergir a zero, salvo se o
multiplicador for zero.
-/
theorem constant_eq_zero_of_tendsto_mul_of_eventually_pos_lower_bound
    {c lower : ℝ} {f : ℕ → ℝ}
    (hlower : 0 < lower)
    (hbound : ∀ᶠ M in atTop, lower ≤ f M)
    (hlim : Tendsto (fun M : ℕ ↦ c * f M) atTop (nhds 0)) :
    c = 0 := by
  by_contra hc
  have hinv :
      Tendsto (fun M : ℕ ↦ c⁻¹ * (c * f M)) atTop
        (nhds (c⁻¹ * 0)) :=
    tendsto_const_nhds.mul hlim
  have hf : Tendsto f atTop (nhds 0) := by
    simpa [mul_assoc, hc] using hinv
  have hlowerZero : lower ≤ 0 := ge_of_tendsto hf hbound
  exact (not_le_of_gt hlower) hlowerZero

/-- Na linha critica, o bulk radial zera e resta somente o bordo acoplado. -/
theorem finiteBracketCoupledCpGreenFlux_tendsto_zero_of_critical
    (p : ℕ) (hp : Nat.Prime p) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hcritical : criticalDisplacement s.re = 0) :
    Tendsto (fun M : ℕ ↦ finiteBracketCoupledCpGreenFlux p M s)
      atTop (nhds 0) := by
  have hboundary :=
    finiteBracketCoupledSignedBoundary_tendsto_zero_of_genuine_zero hs hzero
  have hpoint : ∀ M : ℕ,
      finiteBracketCoupledCpGreenFlux p M s =
        finiteBracketCoupledSignedBoundary M s := by
    intro M
    rw [finiteBracketCoupledCpGreenFlux_eq_radialDifference_mul_pairing
      p M hp s, hcritical]
    simp [cpRadialDifference]
  simpa only [hpoint] using hboundary

/-!
Reciproca rigorosa: se o fluxo acoplado converge a zero num zero Genuine,
entao o deslocamento critico e zero. A prova usa apenas o bordo ja fechado e
o lower positivo fornecido pela primeira aresta.
-/
theorem criticalDisplacement_eq_zero_of_coupledFlux_tendsto_zero
    (p : ℕ) (hp : Nat.Prime p) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hflux :
      Tendsto (fun M : ℕ ↦ finiteBracketCoupledCpGreenFlux p M s)
        atTop (nhds 0)) :
    criticalDisplacement s.re = 0 := by
  let c : ℝ := cpRadialDifference p (criticalDisplacement s.re)
  let pairingRe : ℕ → ℝ :=
    fun M ↦ (finiteReflectedGradientPairing M s).re
  have hboundary :=
    finiteBracketCoupledSignedBoundary_tendsto_zero_of_genuine_zero hs hzero
  have hproduct :
      Tendsto (fun M : ℕ ↦ c * pairingRe M) atTop (nhds 0) := by
    have hsub := hflux.sub hboundary
    have hfun :
        (fun M : ℕ ↦ c * pairingRe M) =
          (fun M : ℕ ↦
            finiteBracketCoupledCpGreenFlux p M s -
              finiteBracketCoupledSignedBoundary M s) := by
      funext M
      dsimp [c, pairingRe]
      rw [finiteBracketCoupledCpGreenFlux_eq_radialDifference_mul_pairing
        p M hp s]
      ring
    rw [hfun]
    simpa using hsub
  have hpositive : 0 < pairingRe 1 := by
    exact finiteReflectedGradientPairing_re_pos (by norm_num) hs
  have hmonotone : Monotone pairingRe := by
    exact finiteReflectedGradientPairing_re_monotone hs
  have hbound : ∀ᶠ M in atTop, pairingRe 1 ≤ pairingRe M :=
    eventually_atTop.2 ⟨1, fun M hM ↦ hmonotone hM⟩
  have hc : c = 0 :=
    constant_eq_zero_of_tendsto_mul_of_eventually_pos_lower_bound
      hpositive hbound hproduct
  have hfactor := cpRadialDifference_eq_two_mul_delta_mul_cofactor
    p (criticalDisplacement s.re)
  have hcofactor := cpRadialCofactor_pos
    p hp (criticalDisplacement s.re)
  dsimp [c] at hc
  nlinarith

/-!
Caracterizacao final deste corte: nos zeros Genuine, anular o fluxo acoplado
no limite e equivalente a ja estar na linha critica.
-/
theorem coupledFlux_tendsto_zero_iff_criticalDisplacement_eq_zero
    (p : ℕ) (hp : Nat.Prime p) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto (fun M : ℕ ↦ finiteBracketCoupledCpGreenFlux p M s)
        atTop (nhds 0) ↔
      criticalDisplacement s.re = 0 := by
  constructor
  · exact criticalDisplacement_eq_zero_of_coupledFlux_tendsto_zero
      p hp hs hzero
  · exact finiteBracketCoupledCpGreenFlux_tendsto_zero_of_critical
      p hp hs hzero

end

end CPFormal.Analytic.Cp
