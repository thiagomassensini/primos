import CPFormal.Analytic.CpGenuineFirstOrthogonalMultibaseGreen
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Passagem ao infinito do operador Genuine ortogonal

As cameras Genuine finitas ja foram identificadas com as cartas bracketadas
finitas e cada carta ja converge para a carta infinita. Este modulo apenas
preserva duas cameras primas como coordenadas ortogonais e transporta essa
convergencia ao nivel de operadores lineares.

Para cutoffs cruzados alinhados, a familia finita e diagonal:

`diag (finiteChart_p / factor_p) (finiteChart_q / factor_q)`.

O operador limite tambem e diagonal e possui o mesmo coeficiente canonico
nas duas coordenadas:

`diag (genuineContinuation s) (genuineContinuation s)`.

A convergencia provada abaixo e forte, isto e, para cada estado do Hilbert de
duas cameras. Nao ha media escalar entre bases e nenhum termo de cutoff e
descartado antes da passagem ao limite.
-/

open scoped BigOperators Topology ComplexConjugate

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-- Hilbert complexo de duas cameras Genuine mantidas separadamente. -/
abbrev TwoPrimeGenuineHilbert := EuclideanSpace ℂ (Fin 2)

/-- Empacotamento complexo canonico das duas cameras. -/
def twoPrimeGenuineVector (x y : ℂ) : TwoPrimeGenuineHilbert :=
  WithLp.toLp 2 fun i => if i = (0 : Fin 2) then x else y

@[simp] theorem twoPrimeGenuineVector_zero (x y : ℂ) :
    twoPrimeGenuineVector x y (0 : Fin 2) = x := by
  simp [twoPrimeGenuineVector]

@[simp] theorem twoPrimeGenuineVector_one (x y : ℂ) :
    twoPrimeGenuineVector x y (1 : Fin 2) = y := by
  norm_num [twoPrimeGenuineVector]

/-- Eixo da primeira camera. -/
def firstPrimeGenuineAxis (x : ℂ) : TwoPrimeGenuineHilbert :=
  twoPrimeGenuineVector x 0

/-- Eixo da segunda camera. -/
def secondPrimeGenuineAxis (y : ℂ) : TwoPrimeGenuineHilbert :=
  twoPrimeGenuineVector 0 y

/-- As duas cameras ocupam eixos ortogonais antes de qualquer sintese. -/
theorem firstPrimeGenuineAxis_inner_secondPrimeGenuineAxis
    (x y : ℂ) :
    inner ℂ (firstPrimeGenuineAxis x) (secondPrimeGenuineAxis y) = 0 := by
  rw [PiLp.inner_apply]
  simp [firstPrimeGenuineAxis, secondPrimeGenuineAxis,
    twoPrimeGenuineVector, Fin.sum_univ_succ]

/-- Continuidade conjunta do empacotamento das duas coordenadas. -/
theorem twoPrimeGenuineVector_tendsto
    {α : Type*} {l : Filter α}
    {x y : α → ℂ} {x₀ y₀ : ℂ}
    (hx : Tendsto x l (nhds x₀))
    (hy : Tendsto y l (nhds y₀)) :
    Tendsto (fun n => twoPrimeGenuineVector (x n) (y n)) l
      (nhds (twoPrimeGenuineVector x₀ y₀)) := by
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
      (p := 2) (β := fun _ : Fin 2 => ℂ)).continuousAt.tendsto.comp hpi
  simpa [twoPrimeGenuineVector, Function.comp_def] using htoLp

/-!
## Cameras normalizadas e seu limite
-/

/-- Camera Genuine finita fora da fatia real-espectral. -/
def finiteNormalizedGenuineCamera
    (p M : ℕ) (s : ℂ) : ℂ :=
  finiteBracketedDirichletChart p M s / cpChartFactor p s

/-- Cada camera prima impar normalizada converge para o Genuine canonico. -/
theorem finiteNormalizedGenuineCamera_tendsto_genuineContinuation
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ => finiteNormalizedGenuineCamera p M s)
      atTop (nhds (genuineContinuation s)) := by
  have hchart :=
    finiteBracketedDirichletChart_tendsto p hp (by linarith [hs.1])
  have hfactor : cpChartFactor p s ≠ 0 :=
    cpChartFactor_ne_zero_on_genuineCriticalStrip p hp hs
  have hchartFactor :=
    bracketedDirichletChart_eq_cpChartFactor_mul_genuineContinuation
      p hp hpodd hs
  have hscaled :
      Tendsto
        (fun M : ℕ =>
          (cpChartFactor p s)⁻¹ * finiteBracketedDirichletChart p M s)
        atTop
        (nhds ((cpChartFactor p s)⁻¹ *
          bracketedDirichletChart p s)) :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (cpChartFactor p s)⁻¹)
        atTop (nhds (cpChartFactor p s)⁻¹)).mul hchart
  have hlimit :
      (cpChartFactor p s)⁻¹ * bracketedDirichletChart p s =
        genuineContinuation s := by
    rw [hchartFactor, ← mul_assoc]
    simp [hfactor]
  rw [hlimit] at hscaled
  simpa only [finiteNormalizedGenuineCamera, div_eq_mul_inv, mul_comm]
    using hscaled

/-- As duas cameras normalizadas nos horizontes cruzados alinhados. -/
def finiteAlignedOrthogonalGenuineVector
    (p q L : ℕ) (s : ℂ) : TwoPrimeGenuineHilbert :=
  twoPrimeGenuineVector
    (finiteNormalizedGenuineCamera p
      (crossPrimeAlignedCutoff q L) s)
    (finiteNormalizedGenuineCamera q
      (crossPrimeAlignedCutoff p L) s)

/-- Vetor Genuine infinito: as duas cameras recuperam o mesmo coeficiente. -/
def orthogonalGenuineLimitVector
    (s : ℂ) : TwoPrimeGenuineHilbert :=
  twoPrimeGenuineVector (genuineContinuation s) (genuineContinuation s)

/-- Passagem ao infinito das cameras alinhadas sem comprimi-las. -/
theorem finiteAlignedOrthogonalGenuineVector_tendsto_limit
    (p q : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Tendsto
      (fun L : ℕ => finiteAlignedOrthogonalGenuineVector p q L s)
      atTop (nhds (orthogonalGenuineLimitVector s)) := by
  have hpCamera :=
    (finiteNormalizedGenuineCamera_tendsto_genuineContinuation
      p hp hpodd hs).comp
        (crossPrimeAlignedCutoff_tendsto_atTop q hq.pos)
  have hqCamera :=
    (finiteNormalizedGenuineCamera_tendsto_genuineContinuation
      q hq hqodd hs).comp
        (crossPrimeAlignedCutoff_tendsto_atTop p hp.pos)
  simpa [finiteAlignedOrthogonalGenuineVector,
    orthogonalGenuineLimitVector] using
      (twoPrimeGenuineVector_tendsto hpCamera hqCamera)

/-!
## Operadores diagonais e convergencia forte
-/

/-- Operador diagonal que age separadamente nas duas cameras. -/
def twoPrimeGenuineDiagonalOperator
    (a b : ℂ) : Module.End ℂ TwoPrimeGenuineHilbert where
  toFun v := twoPrimeGenuineVector
    (a * v (0 : Fin 2)) (b * v (1 : Fin 2))
  map_add' v w := by
    ext i
    fin_cases i <;>
      simp [twoPrimeGenuineVector, mul_add]
  map_smul' c v := by
    ext i
    fin_cases i <;>
      simp [twoPrimeGenuineVector, mul_left_comm]

@[simp] theorem twoPrimeGenuineDiagonalOperator_apply_zero
    (a b : ℂ) (v : TwoPrimeGenuineHilbert) :
    twoPrimeGenuineDiagonalOperator a b v (0 : Fin 2) =
      a * v (0 : Fin 2) := by
  simp [twoPrimeGenuineDiagonalOperator]

@[simp] theorem twoPrimeGenuineDiagonalOperator_apply_one
    (a b : ℂ) (v : TwoPrimeGenuineHilbert) :
    twoPrimeGenuineDiagonalOperator a b v (1 : Fin 2) =
      b * v (1 : Fin 2) := by
  norm_num [twoPrimeGenuineDiagonalOperator]

/-- Operador Genuine ortogonal finito nos cutoffs alinhados. -/
def finiteAlignedOrthogonalGenuineOperator
    (p q L : ℕ) (s : ℂ) : Module.End ℂ TwoPrimeGenuineHilbert :=
  twoPrimeGenuineDiagonalOperator
    (finiteNormalizedGenuineCamera p
      (crossPrimeAlignedCutoff q L) s)
    (finiteNormalizedGenuineCamera q
      (crossPrimeAlignedCutoff p L) s)

/-- Operador Genuine ortogonal no limite. -/
def orthogonalGenuineLimitOperator
    (s : ℂ) : Module.End ℂ TwoPrimeGenuineHilbert :=
  twoPrimeGenuineDiagonalOperator
    (genuineContinuation s) (genuineContinuation s)

/-- O operador limite e multiplicacao escalar pelo Genuine canonico. -/
theorem orthogonalGenuineLimitOperator_apply
    (s : ℂ) (v : TwoPrimeGenuineHilbert) :
    orthogonalGenuineLimitOperator s v = genuineContinuation s • v := by
  ext i
  fin_cases i <;>
    simp [orthogonalGenuineLimitOperator,
      twoPrimeGenuineDiagonalOperator]

/--
Passagem ao infinito em topologia forte: para todo estado de duas cameras,
os operadores finitos alinhados convergem para o Genuine ortogonal limite.
-/
theorem finiteAlignedOrthogonalGenuineOperator_tendsto_apply
    (p q : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (v : TwoPrimeGenuineHilbert) :
    Tendsto
      (fun L : ℕ => finiteAlignedOrthogonalGenuineOperator p q L s v)
      atTop (nhds (orthogonalGenuineLimitOperator s v)) := by
  have hpCamera :=
    (finiteNormalizedGenuineCamera_tendsto_genuineContinuation
      p hp hpodd hs).comp
        (crossPrimeAlignedCutoff_tendsto_atTop q hq.pos)
  have hqCamera :=
    (finiteNormalizedGenuineCamera_tendsto_genuineContinuation
      q hq hqodd hs).comp
        (crossPrimeAlignedCutoff_tendsto_atTop p hp.pos)
  have hpAction :
      Tendsto
        (fun L : ℕ =>
          finiteNormalizedGenuineCamera p
              (crossPrimeAlignedCutoff q L) s *
            v (0 : Fin 2))
        atTop
        (nhds (genuineContinuation s * v (0 : Fin 2))) := by
    simpa [Function.comp_def] using
      hpCamera.mul
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => v (0 : Fin 2))
            atTop (nhds (v (0 : Fin 2))))
  have hqAction :
      Tendsto
        (fun L : ℕ =>
          finiteNormalizedGenuineCamera q
              (crossPrimeAlignedCutoff p L) s *
            v (1 : Fin 2))
        atTop
        (nhds (genuineContinuation s * v (1 : Fin 2))) := by
    simpa [Function.comp_def] using
      hqCamera.mul
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => v (1 : Fin 2))
            atTop (nhds (v (1 : Fin 2))))
  simpa [finiteAlignedOrthogonalGenuineOperator,
    orthogonalGenuineLimitOperator, twoPrimeGenuineDiagonalOperator] using
      (twoPrimeGenuineVector_tendsto hpAction hqAction)

/-- Num zero Genuine, o operador limite e literalmente o operador zero. -/
theorem orthogonalGenuineLimitOperator_eq_zero_of_genuine_zero
    {s : ℂ} (hzero : genuineContinuation s = 0) :
    orthogonalGenuineLimitOperator s = 0 := by
  ext v i
  fin_cases i <;>
    simp [orthogonalGenuineLimitOperator,
      twoPrimeGenuineDiagonalOperator, hzero]

/--
Consequencia operacional do zero Genuine: cada estado finito alinhado
converge para zero nas duas cameras, sem cancelamento cruzado.
-/
theorem finiteAlignedOrthogonalGenuineOperator_tendsto_zero_of_genuine_zero
    (p q : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (v : TwoPrimeGenuineHilbert) :
    Tendsto
      (fun L : ℕ => finiteAlignedOrthogonalGenuineOperator p q L s v)
      atTop (nhds 0) := by
  have hlimit :=
    finiteAlignedOrthogonalGenuineOperator_tendsto_apply
      p q hp hpodd hq hqodd hs v
  rw [orthogonalGenuineLimitOperator_eq_zero_of_genuine_zero hzero] at hlimit
  simpa using hlimit

end

end CPFormal.Analytic.Cp
