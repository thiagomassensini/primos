import CPFormal.Analytic.CpGenuineFirstOrthogonalLimit

/-!
# Limite ortogonal da forma de Green Genuine-first

O operador Genuine ortogonal construido no modulo anterior e o limite das
cameras escalares. A identidade de Green, porem, vive no grafo dos gradientes.
Este modulo realiza a passagem ao infinito nesse segundo objeto sem comprimir
as coordenadas primas.

Primeiro provamos diretamente, por uma estimativa de primeira derivada, que
as arestas refletidas sao absolutamente somaveis no strip. Isso produz uma
energia Green infinita estritamente positiva. Em seguida calculamos o limite
exato de cada fluxo bracketado num zero Genuine:

`lim flux_p = radialDifference_p(delta) * infiniteGreenEnergy`.

Assim as duas cameras possuem um vetor-limite ortogonal explicito. O teorema
de colagem final deste arquivo identifica o nucleo conjunto:

`GenuineOperator = 0` e `GreenLimit = 0`

se, e somente se,

`genuineContinuation s = 0` e `Re(s) = 1/2`.

Isto nao postula que o primeiro nucleo esta contido no segundo. Essa inclusao
e precisamente a ultima relacao de bordo que ainda deve ser demonstrada; ela
nao e escondida numa estrutura ou numa hipotese renomeada.
-/

open scoped BigOperators Topology RealInnerProductSpace

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-! ## Somabilidade absoluta do grafo de gradientes -/

/-- Norma exata da primeira derivada do monomio real de Dirichlet. -/
theorem norm_realDirichletPowerDeriv
    (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖realDirichletPowerDeriv s x‖ =
      ‖s‖ * x ^ (-s.re - 1) := by
  rw [realDirichletPowerDeriv, norm_mul, norm_neg,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  congr 1

/-- Uma diferenca consecutiva compra uma potencia pela primeira derivada. -/
theorem norm_realDirichletPower_succ_sub_le
    {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖realDirichletPower s ((n + 2 : ℕ) : ℝ) -
        realDirichletPower s ((n + 1 : ℕ) : ℝ)‖ ≤
      ‖s‖ * ((n + 1 : ℕ) : ℝ) ^ (-s.re - 1) := by
  have hs0 : s ≠ 0 := by
    intro hzero
    subst s
    norm_num at hs
  let lower : ℝ := ((n + 1 : ℕ) : ℝ)
  let upper : ℝ := ((n + 2 : ℕ) : ℝ)
  have hlower : 0 < lower := by
    dsimp [lower]
    positivity
  have hlowerUpper : lower ≤ upper := by
    dsimp [lower, upper]
    exact_mod_cast Nat.le_succ (n + 1)
  have hlowerMem : lower ∈ Set.Ici lower := by
    exact le_rfl
  have hupperMem : upper ∈ Set.Ici lower :=
    hlowerUpper
  have hderiv :
      ∀ x, x ∈ Set.Ici lower →
        HasDerivWithinAt (realDirichletPower s)
          (realDirichletPowerDeriv s x) (Set.Ici lower) x := by
    intro x hx
    exact (hasDerivAt_realDirichletPower hs0
      (lt_of_lt_of_le hlower hx)).hasDerivWithinAt
  have hbound :
      ∀ x, x ∈ Set.Ici lower →
        ‖realDirichletPowerDeriv s x‖ ≤
          ‖s‖ * lower ^ (-s.re - 1) := by
    intro x hx
    rw [norm_realDirichletPowerDeriv s
      (lt_of_lt_of_le hlower hx)]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hlower hx (by linarith))
      (norm_nonneg s)
  have hlip :=
    (convex_Ici lower).norm_image_sub_le_of_norm_hasDerivWithin_le
      hderiv hbound hlowerMem hupperMem
  have hstep : upper - lower = 1 := by
    dsimp [upper, lower]
    norm_num
  change
    ‖realDirichletPower s upper - realDirichletPower s lower‖ ≤
      ‖s‖ * lower ^ (-s.re - 1)
  calc
    ‖realDirichletPower s upper - realDirichletPower s lower‖ ≤
        (‖s‖ * lower ^ (-s.re - 1)) * ‖upper - lower‖ := hlip
    _ = ‖s‖ * lower ^ (-s.re - 1) := by
      rw [hstep, norm_one, mul_one]

/-- Cota p-serie para um gradiente positivo de Dirichlet. -/
theorem norm_positiveDirichletGradient_le
    {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖positiveDirichletGradient s n‖ ≤
      ‖s‖ * ((n + 1 : ℕ) : ℝ) ^ (-s.re - 1) := by
  rw [positiveDirichletGradient_eq_value_sub_value]
  have hn : n + 1 + 1 = n + 2 := by omega
  simpa [positiveDirichletValue, realDirichletPower, hn] using
    (norm_realDirichletPower_succ_sub_le hs n)

/-- O produto refletido compra tres potencias, uniformemente no strip. -/
theorem norm_finiteReflectedGradientEdge_le
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) (n : ℕ) :
    ‖finiteReflectedGradientEdge n s‖ ≤
      (‖s‖ * ‖reflectedParameter s‖) *
        ((n + 1 : ℕ) : ℝ) ^ (-3 : ℝ) := by
  have hsSharp : reflectedParameter s ∈ genuineCriticalStrip := by
    constructor
    · simpa [reflectedParameter] using
        (show 0 < 1 - s.re by linarith [hs.2])
    · simpa [reflectedParameter] using
        (show 1 - s.re < 1 by linarith [hs.1])
  have hleft := norm_positiveDirichletGradient_le hs.1 n
  have hright := norm_positiveDirichletGradient_le hsSharp.1 n
  have hx : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  unfold finiteReflectedGradientEdge
  rw [norm_mul, Complex.norm_conj]
  calc
    ‖positiveDirichletGradient s n‖ *
        ‖positiveDirichletGradient (reflectedParameter s) n‖ ≤
      (‖s‖ * ((n + 1 : ℕ) : ℝ) ^ (-s.re - 1)) *
        (‖reflectedParameter s‖ *
          ((n + 1 : ℕ) : ℝ) ^
            (-(reflectedParameter s).re - 1)) :=
      mul_le_mul hleft hright (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hx.le _))
    _ = (‖s‖ * ‖reflectedParameter s‖) *
        (((n + 1 : ℕ) : ℝ) ^ (-s.re - 1) *
          ((n + 1 : ℕ) : ℝ) ^
            (-(reflectedParameter s).re - 1)) := by ring
    _ = (‖s‖ * ‖reflectedParameter s‖) *
        ((n + 1 : ℕ) : ℝ) ^
          ((-s.re - 1) + (-(reflectedParameter s).re - 1)) := by
      rw [Real.rpow_add hx]
    _ = (‖s‖ * ‖reflectedParameter s‖) *
        ((n + 1 : ℕ) : ℝ) ^ (-3 : ℝ) := by
      rw [reflectedParameter_re]
      congr 2
      ring

/-- A p-serie deslocada de expoente `-3` e somavel. -/
theorem summable_nat_add_one_rpow_neg_three :
    Summable (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ) ^ (-3 : ℝ)) := by
  have hbase :
      Summable (fun n : ℕ => (n : ℝ) ^ (-3 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hshift := hbase.comp_injective
    (show Function.Injective (fun n : ℕ => n + 1) by
      intro a b hab
      exact Nat.add_right_cancel hab)
  simpa [Function.comp_def] using hshift

/-- As normas das arestas refletidas sao somaveis no strip inteiro. -/
theorem summable_norm_finiteReflectedGradientEdge
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Summable (fun n : ℕ => ‖finiteReflectedGradientEdge n s‖) := by
  have hmajorant := summable_nat_add_one_rpow_neg_three.mul_left
    (‖s‖ * ‖reflectedParameter s‖)
  exact hmajorant.of_norm_bounded fun n => by
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact norm_finiteReflectedGradientEdge_le hs n

/-- A serie complexa de arestas refletidas e absolutamente convergente. -/
theorem summable_finiteReflectedGradientEdge
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Summable (fun n : ℕ => finiteReflectedGradientEdge n s) :=
  (summable_norm_finiteReflectedGradientEdge hs).of_norm

/-- Energia complexa refletida depois da passagem ao infinito. -/
def infiniteReflectedGradientPairing (s : ℂ) : ℂ :=
  ∑' n : ℕ, finiteReflectedGradientEdge n s

/-- Os pareamentos finitos convergem para a energia refletida infinita. -/
theorem finiteReflectedGradientPairing_tendsto_infinite
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Tendsto (fun M : ℕ => finiteReflectedGradientPairing M s)
      atTop (nhds (infiniteReflectedGradientPairing s)) := by
  have hsum := (summable_finiteReflectedGradientEdge hs).tendsto_sum_tsum_nat
  simpa [finiteReflectedGradientPairing, finiteReflectedGradientEdge,
    infiniteReflectedGradientPairing] using hsum

/-- Energia Green real no limite. -/
def infiniteReflectedGreenEnergy (s : ℂ) : ℝ :=
  (infiniteReflectedGradientPairing s).re

/-- Passagem ao limite da energia real. -/
theorem finiteReflectedGradientPairing_re_tendsto_infiniteEnergy
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ => (finiteReflectedGradientPairing M s).re)
      atTop (nhds (infiniteReflectedGreenEnergy s)) := by
  simpa [infiniteReflectedGreenEnergy, Function.comp_def] using
    Complex.continuous_re.continuousAt.tendsto.comp
      (finiteReflectedGradientPairing_tendsto_infinite hs)

/-- A energia Green infinita conserva a positividade estrita da primeira aresta. -/
theorem infiniteReflectedGreenEnergy_pos
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    0 < infiniteReflectedGreenEnergy s := by
  have hfirst : 0 < (finiteReflectedGradientPairing 1 s).re :=
    finiteReflectedGradientPairing_re_pos (by norm_num) hs
  have hbound :
      ∀ᶠ M : ℕ in atTop,
        (finiteReflectedGradientPairing 1 s).re ≤
          (finiteReflectedGradientPairing M s).re :=
    eventually_atTop.2
      ⟨1, fun M hM => finiteReflectedGradientPairing_re_monotone hs hM⟩
  exact lt_of_lt_of_le hfirst
    (ge_of_tendsto
      (finiteReflectedGradientPairing_re_tendsto_infiniteEnergy hs)
      hbound)

/-! ## Limite ortogonal exato do fluxo Green -/

/-- Num zero Genuine, cada fluxo converge para seu bulk radial infinito. -/
theorem finiteBracketCoupledCpGreenFlux_tendsto_infiniteBulk_of_genuine_zero
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
      (fun M : ℕ => finiteBracketCoupledCpGreenFlux p M s)
      atTop
      (nhds
        (cpRadialDifference p (criticalDisplacement s.re) *
          infiniteReflectedGreenEnergy s)) := by
  have hbulk :=
    (tendsto_const_nhds :
      Tendsto
        (fun _ : ℕ => cpRadialDifference p (criticalDisplacement s.re))
        atTop
        (nhds (cpRadialDifference p (criticalDisplacement s.re)))).mul
      (finiteReflectedGradientPairing_re_tendsto_infiniteEnergy hs)
  have hboundary :=
    finiteBracketCoupledSignedBoundary_tendsto_zero_of_genuine_zero hs hzero
  have hsum := hbulk.add hboundary
  have hpoint : ∀ M : ℕ,
      finiteBracketCoupledCpGreenFlux p M s =
        cpRadialDifference p (criticalDisplacement s.re) *
            (finiteReflectedGradientPairing M s).re +
          finiteBracketCoupledSignedBoundary M s := fun M =>
    finiteBracketCoupledCpGreenFlux_eq_radialDifference_mul_pairing
      p M hp s
  simpa only [hpoint, add_zero] using hsum

/-- Vetor de bulk Green que permanece depois que o bordo Genuine fecha. -/
def crossPrimeAlignedGreenLimitVector
    (p q : ℕ) (s : ℂ) : TwoPrimeGreenHilbert :=
  twoPrimeGreenVector
    (cpRadialDifference p (criticalDisplacement s.re) *
      infiniteReflectedGreenEnergy s)
    (cpRadialDifference q (criticalDisplacement s.re) *
      infiniteReflectedGreenEnergy s)

/-- Continuidade conjunta do empacotamento das duas coordenadas reais. -/
theorem twoPrimeGreenVector_tendsto
    {α : Type*} {l : Filter α}
    {x y : α → ℝ} {x₀ y₀ : ℝ}
    (hx : Tendsto x l (nhds x₀))
    (hy : Tendsto y l (nhds y₀)) :
    Tendsto (fun n => twoPrimeGreenVector (x n) (y n)) l
      (nhds (twoPrimeGreenVector x₀ y₀)) := by
  have hpi :
      Tendsto
        (fun n i => if i = (0 : Fin 2) then x n else y n)
        l
        (nhds (fun i => if i = (0 : Fin 2) then x₀ else y₀)) := by
    apply tendsto_pi_nhds.2
    intro i
    fin_cases i
    · simpa using hx
    · simpa using hy
  have htoLp :=
    (PiLp.continuous_toLp
      (p := 2) (β := fun _ : Fin 2 => ℝ)).continuousAt.tendsto.comp hpi
  simpa [twoPrimeGreenVector, Function.comp_def] using htoLp

/-- Passagem ao infinito do vetor Green nos cutoffs cruzados alinhados. -/
theorem crossPrimeAlignedGreenFluxVector_tendsto_limit_of_genuine_zero
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
      (fun L : ℕ => crossPrimeAlignedGreenFluxVector p q L s)
      atTop (nhds (crossPrimeAlignedGreenLimitVector p q s)) := by
  have hpFlux :=
    (finiteBracketCoupledCpGreenFlux_tendsto_infiniteBulk_of_genuine_zero
      p hp hs hzero).comp
        (crossPrimeAlignedCutoff_tendsto_atTop q hq.pos)
  have hqFlux :=
    (finiteBracketCoupledCpGreenFlux_tendsto_infiniteBulk_of_genuine_zero
      q hq hs hzero).comp
        (crossPrimeAlignedCutoff_tendsto_atTop p hp.pos)
  simpa [crossPrimeAlignedGreenFluxVector,
    crossPrimeAlignedGreenLimitVector] using
      (twoPrimeGreenVector_tendsto hpFlux hqFlux)

/-- O vetor Green limite zera exatamente na meia abscissa. -/
theorem crossPrimeAlignedGreenLimitVector_eq_zero_iff_criticalDisplacement_eq_zero
    (p q : ℕ) (hp : Nat.Prime p) (_hq : Nat.Prime q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    crossPrimeAlignedGreenLimitVector p q s = 0 ↔
      criticalDisplacement s.re = 0 := by
  constructor
  · intro hzero
    have hcoordinate := congrArg
      (fun v : TwoPrimeGreenHilbert => v (0 : Fin 2)) hzero
    have hproduct :
        cpRadialDifference p (criticalDisplacement s.re) *
          infiniteReflectedGreenEnergy s = 0 := by
      simpa [crossPrimeAlignedGreenLimitVector] using hcoordinate
    have hradial :
        cpRadialDifference p (criticalDisplacement s.re) = 0 :=
      (mul_eq_zero.mp hproduct).resolve_right
        (ne_of_gt (infiniteReflectedGreenEnergy_pos hs))
    exact (cpRadialDifference_eq_zero_iff
      p hp (criticalDisplacement s.re)).mp hradial
  · intro hcritical
    ext i
    fin_cases i <;>
      simp [crossPrimeAlignedGreenLimitVector, hcritical,
        cpRadialDifference]

/-- Fechamento coordenada a coordenada equivale a anular o vetor-limite. -/
theorem crossPrimeAlignedGreenClosure_iff_limitVector_eq_zero
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    CrossPrimeAlignedGreenClosure p q s ↔
      crossPrimeAlignedGreenLimitVector p q s = 0 := by
  have hpFlux :=
    (finiteBracketCoupledCpGreenFlux_tendsto_infiniteBulk_of_genuine_zero
      p hp hs hzero).comp
        (crossPrimeAlignedCutoff_tendsto_atTop q hq.pos)
  have hqFlux :=
    (finiteBracketCoupledCpGreenFlux_tendsto_infiniteBulk_of_genuine_zero
      q hq hs hzero).comp
        (crossPrimeAlignedCutoff_tendsto_atTop p hp.pos)
  constructor
  · intro hclosure
    have hpZero := tendsto_nhds_unique hpFlux hclosure.1
    have hqZero := tendsto_nhds_unique hqFlux hclosure.2
    ext i
    fin_cases i
    · simpa [crossPrimeAlignedGreenLimitVector] using hpZero
    · simpa [crossPrimeAlignedGreenLimitVector] using hqZero
  · intro hlimit
    constructor
    · have hcoordinate := congrArg
        (fun v : TwoPrimeGreenHilbert => v (0 : Fin 2)) hlimit
      have hpZero :
          cpRadialDifference p (criticalDisplacement s.re) *
            infiniteReflectedGreenEnergy s = 0 := by
        simpa [crossPrimeAlignedGreenLimitVector] using hcoordinate
      simpa [hpZero, Function.comp_def] using hpFlux
    · have hcoordinate := congrArg
        (fun v : TwoPrimeGreenHilbert => v (1 : Fin 2)) hlimit
      have hqZero :
          cpRadialDifference q (criticalDisplacement s.re) *
            infiniteReflectedGreenEnergy s = 0 := by
        simpa [crossPrimeAlignedGreenLimitVector] using hcoordinate
      simpa [hqZero, Function.comp_def] using hqFlux

/-! ## Colagem dos dois limites e exposicao da ultima seta -/

/-- O operador Genuine limite e zero somente se seu coeficiente e zero. -/
theorem orthogonalGenuineLimitOperator_eq_zero_iff
    (s : ℂ) :
    orthogonalGenuineLimitOperator s = 0 ↔
      genuineContinuation s = 0 := by
  constructor
  · intro hop
    have hcoordinate := congrArg
      (fun T : Module.End ℂ TwoPrimeGenuineHilbert =>
        T (firstPrimeGenuineAxis 1) (0 : Fin 2)) hop
    simpa [orthogonalGenuineLimitOperator,
      twoPrimeGenuineDiagonalOperator, firstPrimeGenuineAxis,
      twoPrimeGenuineVector] using hcoordinate
  · exact orthogonalGenuineLimitOperator_eq_zero_of_genuine_zero

/--
Colagem exata dos dois objetos limite. O nucleo conjunto detecta
simultaneamente o zero Genuine e o equilibrio radial critico.
-/
theorem orthogonalGenuineGreenJointKernel_iff
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    (orthogonalGenuineLimitOperator s = 0 ∧
        crossPrimeAlignedGreenLimitVector p q s = 0) ↔
      (genuineContinuation s = 0 ∧
        criticalDisplacement s.re = 0) := by
  rw [orthogonalGenuineLimitOperator_eq_zero_iff,
    crossPrimeAlignedGreenLimitVector_eq_zero_iff_criticalDisplacement_eq_zero
      p q hp hq hs]

end

end CPFormal.Analytic.Cp
