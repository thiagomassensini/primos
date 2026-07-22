import CPFormal.Analytic.CpGenuineFirstMultibaseCutoff
import CPFormal.Analytic.CpBracketGreenFlux
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Green multibase ortogonal Genuine-first

A compressao escalar de duas cameras primas permite cancelamento entre bases
antes que a energia seja medida. Este modulo conserva as cameras como
coordenadas ortogonais de um espaco euclidiano real de dimensao dois.

Nos cutoffs cruzados alinhados, o fluxo Green torna-se a identidade vetorial

`fluxo = bulk radial + bordo bracketado`.

O bordo bracketado fecha em todo zero Genuine. O bulk radial, por outro lado,
e um vetor nao nulo em todo corte sempre que o deslocamento critico nao zera.
Assim, o fechamento coordenada a coordenada do Green multibase e equivalente
a `Re(s) = 1/2`.

O modulo nao assume que todo zero Genuine fecha esse fluxo vetorial. Ele
transforma essa ultima obrigacao numa interface concreta sem compressao
escalar e sem interferencia entre cameras.
-/

open scoped BigOperators Topology RealInnerProductSpace

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-- Duas cameras primas mantidas como coordenadas ortogonais reais. -/
abbrev TwoPrimeGreenHilbert := EuclideanSpace ℝ (Fin 2)

/-- Empacotamento canonico de dois readouts sem soma-los. -/
def twoPrimeGreenVector (x y : ℝ) : TwoPrimeGreenHilbert :=
  WithLp.toLp 2 fun i => if i = (0 : Fin 2) then x else y

@[simp] theorem twoPrimeGreenVector_zero (x y : ℝ) :
    twoPrimeGreenVector x y (0 : Fin 2) = x := by
  simp [twoPrimeGreenVector]

@[simp] theorem twoPrimeGreenVector_one (x y : ℝ) :
    twoPrimeGreenVector x y (1 : Fin 2) = y := by
  norm_num [twoPrimeGreenVector]

/--
A energia interna do vetor de duas cameras e a soma das duas energias
coordenadas. Nao aparece termo cruzado entre os primos.
-/
theorem twoPrimeGreenVector_inner_self (x y : ℝ) :
    inner ℝ (twoPrimeGreenVector x y) (twoPrimeGreenVector x y) =
      x ^ 2 + y ^ 2 := by
  rw [PiLp.inner_apply]
  simp [twoPrimeGreenVector, Fin.sum_univ_succ]
  ring

/-- Todo cutoff cruzado por um primo impar e nao vazio. -/
theorem crossPrimeAlignedCutoff_pos
    (other L : ℕ) (hother : Nat.Prime other) (hotherOdd : Odd other) :
    0 < crossPrimeAlignedCutoff other L := by
  have hform :=
    CPFormal.Carry.Cp.two_mul_halfRange_add_one hotherOdd
  have hone := hother.one_lt
  unfold crossPrimeAlignedCutoff
  omega

/-- As duas correntes Green nos horizontes cruzados alinhados. -/
def crossPrimeAlignedGreenFluxVector
    (p q L : ℕ) (s : ℂ) : TwoPrimeGreenHilbert :=
  twoPrimeGreenVector
    (finiteBracketCoupledCpGreenFlux p
      (crossPrimeAlignedCutoff q L) s)
    (finiteBracketCoupledCpGreenFlux q
      (crossPrimeAlignedCutoff p L) s)

/-- Bulk radial positivo mantido separadamente em cada camera. -/
def crossPrimeAlignedRadialBulkVector
    (p q L : ℕ) (s : ℂ) : TwoPrimeGreenHilbert :=
  twoPrimeGreenVector
    (2 * criticalDisplacement s.re *
      finiteRadialGreenEnergy p (crossPrimeAlignedCutoff q L) s)
    (2 * criticalDisplacement s.re *
      finiteRadialGreenEnergy q (crossPrimeAlignedCutoff p L) s)

/-- Bordos bracketados das duas cameras, sem mistura entre bases. -/
def crossPrimeAlignedGreenBoundaryVector
    (p q L : ℕ) (s : ℂ) : TwoPrimeGreenHilbert :=
  twoPrimeGreenVector
    (finiteBracketCoupledSignedBoundary
      (crossPrimeAlignedCutoff q L) s)
    (finiteBracketCoupledSignedBoundary
      (crossPrimeAlignedCutoff p L) s)

/--
Identidade Green multibase em forma vetorial. Cada coordenada preserva sua
propria identidade Green; nenhuma media escalar e aplicada.
-/
theorem crossPrimeAlignedGreenFluxVector_eq_radial_add_boundary
    (p q L : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (s : ℂ) :
    crossPrimeAlignedGreenFluxVector p q L s =
      crossPrimeAlignedRadialBulkVector p q L s +
        crossPrimeAlignedGreenBoundaryVector p q L s := by
  ext i
  fin_cases i
  · change
      finiteBracketCoupledCpGreenFlux p
          (crossPrimeAlignedCutoff q L) s =
        2 * criticalDisplacement s.re *
            finiteRadialGreenEnergy p
              (crossPrimeAlignedCutoff q L) s +
          finiteBracketCoupledSignedBoundary
            (crossPrimeAlignedCutoff q L) s
    exact finiteBracketCoupledCpGreen_identity
      p (crossPrimeAlignedCutoff q L) hp s
  · change
      finiteBracketCoupledCpGreenFlux q
          (crossPrimeAlignedCutoff p L) s =
        2 * criticalDisplacement s.re *
            finiteRadialGreenEnergy q
              (crossPrimeAlignedCutoff p L) s +
          finiteBracketCoupledSignedBoundary
            (crossPrimeAlignedCutoff p L) s
    exact finiteBracketCoupledCpGreen_identity
      q (crossPrimeAlignedCutoff p L) hq s

/-- Ledger pitagorico explicito para o bulk radial das duas cameras. -/
theorem crossPrimeAlignedRadialBulkVector_inner_self
    (p q L : ℕ) (s : ℂ) :
    inner ℝ (crossPrimeAlignedRadialBulkVector p q L s)
      (crossPrimeAlignedRadialBulkVector p q L s) =
      (2 * criticalDisplacement s.re *
        finiteRadialGreenEnergy p
          (crossPrimeAlignedCutoff q L) s) ^ 2 +
      (2 * criticalDisplacement s.re *
        finiteRadialGreenEnergy q
          (crossPrimeAlignedCutoff p L) s) ^ 2 := by
  exact twoPrimeGreenVector_inner_self _ _

/--
No strip, o vetor de bulk radial zera exatamente na meia abscissa. Uma unica
coordenada ja bastaria; a forma vetorial registra que cameras diferentes nao
podem se cancelar entre si.
-/
theorem crossPrimeAlignedRadialBulkVector_eq_zero_iff_criticalDisplacement_eq_zero
    (p q L : ℕ)
    (hp : Nat.Prime p) (_hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    crossPrimeAlignedRadialBulkVector p q L s = 0 ↔
      criticalDisplacement s.re = 0 := by
  constructor
  · intro hzero
    have hcoordinate := congrArg
      (fun v : TwoPrimeGreenHilbert => v (0 : Fin 2)) hzero
    have hcoordinate' :
        2 * criticalDisplacement s.re *
          finiteRadialGreenEnergy p
            (crossPrimeAlignedCutoff q L) s = 0 := by
      simpa [crossPrimeAlignedRadialBulkVector] using hcoordinate
    have henergy :
        0 < finiteRadialGreenEnergy p
          (crossPrimeAlignedCutoff q L) s :=
      finiteRadialGreenEnergy_pos p
        (crossPrimeAlignedCutoff q L) hp
        (crossPrimeAlignedCutoff_pos q L hq hqodd) hs
    have hmul :
        criticalDisplacement s.re *
          finiteRadialGreenEnergy p
            (crossPrimeAlignedCutoff q L) s = 0 := by
      linarith
    exact (mul_eq_zero.mp hmul).resolve_right (ne_of_gt henergy)
  · intro hcritical
    ext i
    fin_cases i <;>
      simp [crossPrimeAlignedRadialBulkVector, hcritical]

/-- Soma das energias dos dois bordos, ainda sem termo cruzado entre bases. -/
def crossPrimeAlignedGreenBoundaryEnergy
    (p q L : ℕ) (s : ℂ) : ℝ :=
  (finiteBracketCoupledSignedBoundary
      (crossPrimeAlignedCutoff q L) s) ^ 2 +
    (finiteBracketCoupledSignedBoundary
      (crossPrimeAlignedCutoff p L) s) ^ 2

/-- A energia de bordo e literalmente o produto interno do vetor de bordo. -/
theorem crossPrimeAlignedGreenBoundaryVector_inner_self
    (p q L : ℕ) (s : ℂ) :
    inner ℝ (crossPrimeAlignedGreenBoundaryVector p q L s)
      (crossPrimeAlignedGreenBoundaryVector p q L s) =
      crossPrimeAlignedGreenBoundaryEnergy p q L s := by
  exact twoPrimeGreenVector_inner_self _ _

/--
Num zero Genuine, os dois bordos alinhados fecham simultaneamente em energia.
A informacao de cutoff nao e descartada: cada coordenada converge por sua
propria cauda bracketada.
-/
theorem crossPrimeAlignedGreenBoundaryEnergy_tendsto_zero_of_genuine_zero
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
      (fun L : ℕ => crossPrimeAlignedGreenBoundaryEnergy p q L s)
      atTop (nhds 0) := by
  have hboundary :=
    finiteBracketCoupledSignedBoundary_tendsto_zero_of_genuine_zero hs hzero
  have hpBoundary :=
    hboundary.comp
      (crossPrimeAlignedCutoff_tendsto_atTop q hq.pos)
  have hqBoundary :=
    hboundary.comp
      (crossPrimeAlignedCutoff_tendsto_atTop p hp.pos)
  have hpSquare := hpBoundary.mul hpBoundary
  have hqSquare := hqBoundary.mul hqBoundary
  simpa [crossPrimeAlignedGreenBoundaryEnergy, Function.comp_def, pow_two]
    using hpSquare.add hqSquare

/--
Fechamento Green multibase sem compressao: cada coordenada prima converge
separadamente para zero.
-/
def CrossPrimeAlignedGreenClosure
    (p q : ℕ) (s : ℂ) : Prop :=
  Tendsto
      (fun L : ℕ =>
        finiteBracketCoupledCpGreenFlux p
          (crossPrimeAlignedCutoff q L) s)
      atTop (nhds 0) ∧
    Tendsto
      (fun L : ℕ =>
        finiteBracketCoupledCpGreenFlux q
          (crossPrimeAlignedCutoff p L) s)
      atTop (nhds 0)

/-- Na meia abscissa, um zero Genuine fecha as duas coordenadas Green. -/
theorem crossPrimeAlignedGreenClosure_of_critical
    (p q : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hcritical : criticalDisplacement s.re = 0) :
    CrossPrimeAlignedGreenClosure p q s := by
  constructor
  · exact
      (finiteBracketCoupledCpGreenFlux_tendsto_zero_of_critical
        p hp hs hzero hcritical).comp
          (crossPrimeAlignedCutoff_tendsto_atTop q hq.pos)
  · exact
      (finiteBracketCoupledCpGreenFlux_tendsto_zero_of_critical
        q hq hs hzero hcritical).comp
          (crossPrimeAlignedCutoff_tendsto_atTop p hp.pos)

/--
Se uma coordenada Green alinhada fecha num zero Genuine, a positividade do
bulk radial ja obriga a meia abscissa.
-/
theorem criticalDisplacement_eq_zero_of_crossPrimeAlignedGreenFlux_tendsto_zero
    (p q : ℕ)
    (hp : Nat.Prime p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hflux :
      Tendsto
        (fun L : ℕ =>
          finiteBracketCoupledCpGreenFlux p
            (crossPrimeAlignedCutoff q L) s)
        atTop (nhds 0)) :
    criticalDisplacement s.re = 0 := by
  let c : ℝ := cpRadialDifference p (criticalDisplacement s.re)
  let pairingRe : ℕ → ℝ :=
    fun L =>
      (finiteReflectedGradientPairing
        (crossPrimeAlignedCutoff q L) s).re
  have hboundary :=
    (finiteBracketCoupledSignedBoundary_tendsto_zero_of_genuine_zero
      hs hzero).comp
        (crossPrimeAlignedCutoff_tendsto_atTop q hq.pos)
  have hproduct :
      Tendsto (fun L : ℕ => c * pairingRe L) atTop (nhds 0) := by
    have hsub := hflux.sub hboundary
    have hfun :
        (fun L : ℕ => c * pairingRe L) =
          (fun L : ℕ =>
            finiteBracketCoupledCpGreenFlux p
                (crossPrimeAlignedCutoff q L) s -
              finiteBracketCoupledSignedBoundary
                (crossPrimeAlignedCutoff q L) s) := by
      funext L
      rw [finiteBracketCoupledCpGreenFlux_eq_radialDifference_mul_pairing
        p (crossPrimeAlignedCutoff q L) hp s]
      dsimp [c, pairingRe]
      ring
    rw [hfun]
    simpa using hsub
  have hpositive :
      0 < (finiteReflectedGradientPairing 1 s).re :=
    finiteReflectedGradientPairing_re_pos (by norm_num) hs
  have hmonotone :=
    finiteReflectedGradientPairing_re_monotone hs
  have hbound :
      ∀ᶠ L in atTop,
        (finiteReflectedGradientPairing 1 s).re ≤ pairingRe L :=
    Eventually.of_forall fun L =>
      hmonotone (crossPrimeAlignedCutoff_pos q L hq hqodd)
  have hc : c = 0 :=
    constant_eq_zero_of_tendsto_mul_of_eventually_pos_lower_bound
      hpositive hbound hproduct
  dsimp [c] at hc
  exact (cpRadialDifference_eq_zero_iff
    p hp (criticalDisplacement s.re)).mp hc

/--
Caracterizacao do fechamento ortogonal: em zeros Genuine, fechar as cameras
coordenada a coordenada equivale exatamente a estar na linha critica.
-/
theorem crossPrimeAlignedGreenClosure_iff_criticalDisplacement_eq_zero
    (p q : ℕ)
    (hp : Nat.Prime p) (_hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    CrossPrimeAlignedGreenClosure p q s ↔
      criticalDisplacement s.re = 0 := by
  constructor
  · intro hclosure
    exact
      criticalDisplacement_eq_zero_of_crossPrimeAlignedGreenFlux_tendsto_zero
        p q hp hq hqodd hs hzero hclosure.1
  · exact crossPrimeAlignedGreenClosure_of_critical
      p q hp hq hs hzero

/--
A mesma caracterizacao comparada ao bulk finito: qualquer horizonte alinhado
ja reconhece o unico ponto onde o vetor radial pode zerar.
-/
theorem crossPrimeAlignedGreenClosure_iff_radialBulkVector_eq_zero
    (p q L : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    CrossPrimeAlignedGreenClosure p q s ↔
      crossPrimeAlignedRadialBulkVector p q L s = 0 := by
  rw [crossPrimeAlignedGreenClosure_iff_criticalDisplacement_eq_zero
      p q hp hpodd hq hqodd hs hzero,
    crossPrimeAlignedRadialBulkVector_eq_zero_iff_criticalDisplacement_eq_zero
      p q L hp hpodd hq hqodd hs]

end

end CPFormal.Analytic.Cp
