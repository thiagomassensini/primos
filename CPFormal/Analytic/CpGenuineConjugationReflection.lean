import CPFormal.Analytic.CpFiniteGenuineAngularGreenBudget

/-!
# Estrutura real do Genuine e reflexao central

O checkpoint 0.38 isolou a estabilidade de zeros sob

`s# = 1 - conj(s)`

como uma das duas obrigacoes restantes. Este arquivo separa as duas operacoes
que aparecem nessa expressao. A conjugacao e automatica: os monomios, os
gradientes, a porta angular, a carta bracketada e o quociente Genuine
preservam a estrutura real. Consequentemente,

`G(1-conj(s)) = conj(G(1-s))`.

Assim, a estabilidade de zeros sob `s#` e exatamente equivalente a
estabilidade sob `s -> 1-s`. A conjugacao nao e mais uma hipotese escondida;
a unica dualidade central ainda aberta e a transformacao `1-s`.
-/

open scoped BigOperators Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-!
## Conjugacao termo a termo da porta angular
-/

/-- Um valor positivo de Dirichlet preserva a estrutura real do parametro. -/
@[simp] theorem positiveDirichletValue_conj
    (s : ℂ) (n : ℕ) :
    positiveDirichletValue ((starRingEnd ℂ) s) n =
      (starRingEnd ℂ) (positiveDirichletValue s n) := by
  let x : ℂ := ((n + 1 : ℕ) : ℂ)
  have hxconj : (starRingEnd ℂ) x = x := by
    simp [x]
  have hargzero : x.arg = 0 := by
    simpa [x] using (Complex.natCast_arg (n := n + 1))
  have harg : x.arg ≠ Real.pi := by
    rw [hargzero]
    exact Real.pi_ne_zero.symm
  have hconj :
      (starRingEnd ℂ) (x ^ (-s)) =
        x ^ (-(starRingEnd ℂ) s) := by
    have h := (Complex.cpow_conj x (-s) harg).symm
    rw [hxconj] at h
    simpa using h
  unfold positiveDirichletValue
  change x ^ (-(starRingEnd ℂ) s) =
    (starRingEnd ℂ) (x ^ (-s))
  exact hconj.symm

/-- O gradiente positivo comuta com conjugacao. -/
@[simp] theorem positiveDirichletGradient_conj
    (s : ℂ) (n : ℕ) :
    positiveDirichletGradient ((starRingEnd ℂ) s) n =
      (starRingEnd ℂ) (positiveDirichletGradient s n) := by
  rw [positiveDirichletGradient_eq_value_sub_value,
    positiveDirichletGradient_eq_value_sub_value]
  simp only [positiveDirichletValue_conj, map_sub]

/-- Cada bloco angular comuta com conjugacao antes de qualquer limite. -/
@[simp] theorem canonicalAngularGradientBlock_conj
    (m : ℕ) (s : ℂ) :
    canonicalAngularGradientBlock m ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (canonicalAngularGradientBlock m s) := by
  rw [canonicalAngularGradientBlock_eq_two_edges,
    canonicalAngularGradientBlock_eq_two_edges]
  simp only [positiveDirichletGradient_conj, map_neg, map_add, map_mul]
  have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    exact Complex.conj_ofNat 2
  rw [htwo]

/-- Todo cutoff da porta angular preserva a estrutura real. -/
@[simp] theorem finiteCanonicalAngularTrace_conj
    (M : ℕ) (s : ℂ) :
    finiteCanonicalAngularTrace M ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (finiteCanonicalAngularTrace M s) := by
  unfold finiteCanonicalAngularTrace
  simp_rw [canonicalAngularGradientBlock_conj]
  rw [map_sum]

/-!
## Conjugacao da carta e do Genuine canonico
-/

/-- A carta bracketada canonica herda conjugacao dos cutoffs angulares. -/
theorem bracketedDirichletChart_three_conj
    {s : ℂ} (hs : 0 < s.re) :
    bracketedDirichletChart 3 ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (bracketedDirichletChart 3 s) := by
  have hsConj : 0 < ((starRingEnd ℂ) s).re := by
    simpa using hs
  have hleft :=
    finiteCanonicalAngularTrace_tendsto (s := (starRingEnd ℂ) s) hsConj
  have hleft' :
      Tendsto
        (fun M : ℕ ↦
          (starRingEnd ℂ) (finiteCanonicalAngularTrace M s))
        atTop
        (nhds (bracketedDirichletChart 3 ((starRingEnd ℂ) s))) := by
    simpa only [finiteCanonicalAngularTrace_conj] using hleft
  have hbase := finiteCanonicalAngularTrace_tendsto (s := s) hs
  have hright :
      Tendsto
        (fun M : ℕ ↦
          (starRingEnd ℂ) (finiteCanonicalAngularTrace M s))
        atTop
        (nhds ((starRingEnd ℂ) (bracketedDirichletChart 3 s))) := by
    simpa [Function.comp_def] using
      (Complex.continuous_conj.tendsto
        (bracketedDirichletChart 3 s)).comp hbase
  exact tendsto_nhds_unique hleft' hright

/-- O fator da camera `p=3` tambem preserva a estrutura real. -/
theorem cpChartFactor_three_conj (s : ℂ) :
    cpChartFactor 3 ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (cpChartFactor 3 s) := by
  let x : ℂ := (3 : ℂ)
  have hxconj : (starRingEnd ℂ) x = x := by
    simp [x]
  have hargzero : x.arg = 0 := by
    simpa [x] using (Complex.natCast_arg (n := 3))
  have harg : x.arg ≠ Real.pi := by
    rw [hargzero]
    exact Real.pi_ne_zero.symm
  have hconjPower :
      (starRingEnd ℂ) (x ^ (1 - s)) =
        x ^ ((starRingEnd ℂ) (1 - s)) := by
    have h := (Complex.cpow_conj x (1 - s) harg).symm
    rw [hxconj] at h
    simpa using h
  unfold cpChartFactor
  change 1 - x ^ (1 - (starRingEnd ℂ) s) =
    (starRingEnd ℂ) (1 - x ^ (1 - s))
  calc
    1 - x ^ (1 - (starRingEnd ℂ) s) =
        1 - x ^ ((starRingEnd ℂ) (1 - s)) := by
      simp only [map_sub, map_one]
    _ = (starRingEnd ℂ) (1 - x ^ (1 - s)) := by
      rw [map_sub, map_one, hconjPower]

/-- No strip Genuine, a continuacao canonica e uma funcao de estrutura real. -/
theorem genuineContinuation_conj
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    genuineContinuation ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (genuineContinuation s) := by
  unfold genuineContinuation cpGenuineQuotient
  rw [bracketedDirichletChart_three_conj hs.1,
    cpChartFactor_three_conj, map_div]

/-- Em particular, os zeros Genuine sao automaticamente conjugados. -/
theorem genuineContinuation_conj_zero_iff
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    genuineContinuation ((starRingEnd ℂ) s) = 0 ↔
      genuineContinuation s = 0 := by
  rw [genuineContinuation_conj hs]
  constructor
  · intro h
    have hc := congrArg (starRingEnd ℂ) h
    simpa using hc
  · intro h
    rw [h]
    simp

/-!
## Separacao da reflexao central
-/

/-- A transformacao sem conjugacao `s -> 1-s` preserva o strip. -/
theorem one_sub_mem_genuineCriticalStrip
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    1 - s ∈ genuineCriticalStrip := by
  constructor
  · simpa using (show 0 < 1 - s.re by linarith [hs.2])
  · simpa using (show 1 - s.re < 1 by linarith [hs.1])

/-- A reflexao Green e conjugacao aplicada ao parametro `1-s`. -/
theorem genuineContinuation_reflectedParameter_eq_conj_one_sub
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    genuineContinuation (reflectedParameter s) =
      (starRingEnd ℂ) (genuineContinuation (1 - s)) := by
  have h := genuineContinuation_conj
    (s := 1 - s) (one_sub_mem_genuineCriticalStrip hs)
  simpa [reflectedParameter] using h

/-- Zero em `s#` e exatamente zero em `1-s`; a conjugacao e automatica. -/
theorem genuineContinuation_reflectedParameter_zero_iff_one_sub
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    genuineContinuation (reflectedParameter s) = 0 ↔
      genuineContinuation (1 - s) = 0 := by
  rw [genuineContinuation_reflectedParameter_eq_conj_one_sub hs]
  constructor
  · intro h
    have hc := congrArg (starRingEnd ℂ) h
    simpa using hc
  · intro h
    rw [h]
    simp

/-!
Uma funcao de estrutura real nao precisa ter simetria central. Este witness
impede que a conjugacao provada acima seja confundida com a obrigacao
`s -> 1-s`.
-/
theorem real_structure_does_not_force_one_sub_zero :
    ∃ F : ℂ → ℂ,
      (∀ s : ℂ,
        F ((starRingEnd ℂ) s) = (starRingEnd ℂ) (F s)) ∧
      F (((1 / 3 : ℝ) : ℂ)) = 0 ∧
      F (1 - (((1 / 3 : ℝ) : ℂ))) ≠ 0 := by
  refine ⟨fun s : ℂ ↦ s - (((1 / 3 : ℝ) : ℂ)), ?_, ?_, ?_⟩
  · intro s
    simp
  · norm_num
  · norm_num

/-!
## Ponte equivalente com a obrigacao central exposta
-/

/--
Versao do bridge do 0.38 em que a unica simetria de zeros pedida e
literalmente `s -> 1-s`. A conjugacao ja foi descarregada pelo kernel.
-/
structure GenuineOneSubAngularGreenCancellationBridge (p : ℕ) : Prop where
  one_sub_zero :
    ∀ {s : ℂ}, genuineContinuation s = 0 →
      s ∈ genuineCriticalStrip →
      genuineContinuation (1 - s) = 0
  scaled_correction_closes :
    ∀ {s : ℂ}, genuineContinuation s = 0 →
      s ∈ genuineCriticalStrip →
      Tendsto
        (fun M : ℕ ↦
          ((cpRadialDifference p (criticalDisplacement s.re) : ℝ) : ℂ) *
            finiteCanonicalAngularGreenCorrection M s)
        atTop (nhds 0)

/-- A ponte `1-s` constroi a ponte refletida do 0.38. -/
theorem GenuineOneSubAngularGreenCancellationBridge.toReflectedBridge
    {p : ℕ} (bridge : GenuineOneSubAngularGreenCancellationBridge p) :
    GenuineAngularGreenCancellationBridge p := by
  refine ⟨?_, ?_⟩
  · intro s hzero hs
    exact
      (genuineContinuation_reflectedParameter_zero_iff_one_sub hs).2
        (bridge.one_sub_zero hzero hs)
  · intro s hzero hs
    exact bridge.scaled_correction_closes hzero hs

/-- A ponte refletida do 0.38 recupera a formulacao equivalente em `1-s`. -/
theorem GenuineAngularGreenCancellationBridge.toOneSubBridge
    {p : ℕ} (bridge : GenuineAngularGreenCancellationBridge p) :
    GenuineOneSubAngularGreenCancellationBridge p := by
  refine ⟨?_, ?_⟩
  · intro s hzero hs
    exact
      (genuineContinuation_reflectedParameter_zero_iff_one_sub hs).1
        (bridge.reflected_zero hzero hs)
  · intro s hzero hs
    exact bridge.scaled_correction_closes hzero hs

/-- As duas interfaces sao logicamente equivalentes, sem hipotese adicional. -/
theorem genuineOneSubBridge_iff_reflectedBridge (p : ℕ) :
    GenuineOneSubAngularGreenCancellationBridge p ↔
      GenuineAngularGreenCancellationBridge p := by
  constructor
  · exact GenuineOneSubAngularGreenCancellationBridge.toReflectedBridge
  · exact GenuineAngularGreenCancellationBridge.toOneSubBridge

/-- Sob a dualidade `1-s` e o fechamento da correcao, o tilt zera. -/
theorem GenuineOneSubAngularGreenCancellationBridge.criticalDisplacement_eq_zero
    {p : ℕ} (hp : Nat.Prime p)
    (bridge : GenuineOneSubAngularGreenCancellationBridge p)
    {s : ℂ} (hzero : genuineContinuation s = 0)
    (hs : s ∈ genuineCriticalStrip) :
    criticalDisplacement s.re = 0 :=
  bridge.toReflectedBridge.criticalDisplacement_eq_zero hp hzero hs

/-- A nova interface tambem constroi diretamente a ponte carry--Green. -/
theorem GenuineOneSubAngularGreenCancellationBridge.toGenuineCarryFluxBridge
    {p : ℕ} (hp : Nat.Prime p)
    (bridge : GenuineOneSubAngularGreenCancellationBridge p) :
    GenuineCarryFluxBridge p :=
  bridge.toReflectedBridge.toGenuineCarryFluxBridge hp

end

end CPFormal.Analytic.Cp
