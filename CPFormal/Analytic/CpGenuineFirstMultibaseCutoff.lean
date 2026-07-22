import CPFormal.Analytic.CpGenuineFirstCutoffTail

/-!
# Escalas multibase alinhadas e sincronizacao vertical

Para primos impares `p` e `q`, existe uma familia inteira de cutoffs que
termina no mesmo horizonte horizontal:

`M_p(L) = q * L + halfRange q`,
`M_q(L) = p * L + halfRange p`.

Este modulo prova que o defeito horizontal--vertical desses cortes continua
sendo o mesmo detector Genuine em toda escala. Como as caudas de uma serie
bracketada somavel tendem a zero, um zero Genuine obriga as correcoes
verticais das duas bases a se sincronizarem assintoticamente.

A forma final usa somente prefixos finitos de Dirichlet e pesos de base; nao
usa zeta, equacao funcional ou tabela de zeros.
-/

open scoped BigOperators Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-- Cutoff na camera atual determinado pela outra base e pela escala `L`. -/
def crossPrimeAlignedCutoff (other L : ℕ) : ℕ :=
  other * L + CPFormal.Genuine.Cp.halfRange other

/--
Em toda escala, os cutoffs cruzados de `p` e `q` ladrilham exatamente o
mesmo prefixo horizontal.
-/
theorem blockPrefix_cross_prime_aligned_scale
    (p q L : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    (f : ℤ → ℂ) :
    CPFormal.Genuine.Cp.blockPrefix p
        (crossPrimeAlignedCutoff q L) f =
      CPFormal.Genuine.Cp.blockPrefix q
        (crossPrimeAlignedCutoff p L) f := by
  rw [CPFormal.Genuine.Cp.blockPrefix_eq_positiveIntervalSum
      p hp hpodd,
    CPFormal.Genuine.Cp.blockPrefix_eq_positiveIntervalSum
      q hq hqodd]
  have hpformNat :=
    CPFormal.Carry.Cp.two_mul_halfRange_add_one hpodd
  have hqformNat :=
    CPFormal.Carry.Cp.two_mul_halfRange_add_one hqodd
  have hpformInt :
      (p : ℤ) =
        2 * (CPFormal.Genuine.Cp.halfRange p : ℤ) + 1 := by
    exact_mod_cast hpformNat.symm
  have hqformInt :
      (q : ℤ) =
        2 * (CPFormal.Genuine.Cp.halfRange q : ℤ) + 1 := by
    exact_mod_cast hqformNat.symm
  have hend :
      (p : ℤ) * ((crossPrimeAlignedCutoff q L : ℕ) : ℤ) +
          (CPFormal.Genuine.Cp.halfRange p : ℤ) =
        (q : ℤ) * ((crossPrimeAlignedCutoff p L : ℕ) : ℤ) +
          (CPFormal.Genuine.Cp.halfRange q : ℤ) := by
    unfold crossPrimeAlignedCutoff
    push_cast
    rw [hpformInt, hqformInt]
    ring
  rw [hend]

/-- Defeito multibase na escala alinhada `L`. -/
def crossPrimeAlignedCutoffDefect
    (p q L : ℕ) (s : ℂ) : ℂ :=
  (CPFormal.Genuine.Cp.verticalCorrection p
      (crossPrimeAlignedCutoff q L) (dirichletTerm s) -
    realCpBracketCutoffTail p (crossPrimeAlignedCutoff q L) s) -
  (CPFormal.Genuine.Cp.verticalCorrection q
      (crossPrimeAlignedCutoff p L) (dirichletTerm s) -
    realCpBracketCutoffTail q (crossPrimeAlignedCutoff p L) s)

/-- O defeito alinhado continua sendo a diferenca das duas cartas infinitas. -/
theorem crossPrimeAlignedCutoffDefect_eq_chart_sub_chart
    (p q L : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : -1 < s.re) :
    crossPrimeAlignedCutoffDefect p q L s =
      bracketedDirichletChart q s - bracketedDirichletChart p s := by
  unfold crossPrimeAlignedCutoffDefect
  rw [verticalCorrection_sub_cutoffTail_eq_blockPrefix_sub_chart
      p (crossPrimeAlignedCutoff q L) hp hpodd hs,
    verticalCorrection_sub_cutoffTail_eq_blockPrefix_sub_chart
      q (crossPrimeAlignedCutoff p L) hq hqodd hs,
    blockPrefix_cross_prime_aligned_scale
      p q L hp hpodd hq hqodd (dirichletTerm s)]
  ring

/--
O detector e independente da escala: em todo `L`, ele fatora pela diferenca
dos fatores de camera e pelo mesmo Genuine.
-/
theorem crossPrimeAlignedCutoffDefect_eq_factor_sub_mul_genuine
    (p q L : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    crossPrimeAlignedCutoffDefect p q L s =
      (cpChartFactor q s - cpChartFactor p s) *
        genuineContinuation s := by
  rw [crossPrimeAlignedCutoffDefect_eq_chart_sub_chart
      p q L hp hpodd hq hqodd (by linarith [hs.1]),
    bracketedDirichletChart_eq_cpChartFactor_mul_genuineContinuation
      q hq hqodd hs,
    bracketedDirichletChart_eq_cpChartFactor_mul_genuineContinuation
      p hp hpodd hs]
  ring

/-- Em cada escala alinhada, fechar o detector equivale a zerar o Genuine. -/
theorem crossPrimeAlignedCutoffDefect_eq_zero_iff_genuine_zero
    (p q L : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    (hpq : p ≠ q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    crossPrimeAlignedCutoffDefect p q L s = 0 ↔
      genuineContinuation s = 0 := by
  rw [crossPrimeAlignedCutoffDefect_eq_factor_sub_mul_genuine
      p q L hp hpodd hq hqodd hs]
  exact mul_eq_zero_iff_left
    (cpChartFactor_sub_ne_zero_of_distinct_primes_on_strip
      p q hp hq hpq hs)

/--
A cauda bracketada tende a zero. O valor do cutoff e mantido como a diferenca
exata entre a soma infinita e seu prefixo, sem descartar nenhum termo.
-/
theorem realCpBracketCutoffTail_tendsto_zero
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : -1 < s.re) :
    Tendsto (fun M : ℕ ↦ realCpBracketCutoffTail p M s)
      atTop (nhds 0) := by
  have hsum := summable_realCpSaturatedBracket p hp hs
  have hpartial := hsum.tendsto_sum_tsum_nat
  have hconstant :
      Tendsto
        (fun _ : ℕ ↦ ∑' k : ℕ, realCpSaturatedBracket p k s)
        atTop
        (nhds (∑' k : ℕ, realCpSaturatedBracket p k s)) :=
    tendsto_const_nhds
  have hlimit :
      Tendsto
        (fun M : ℕ ↦
          (∑' k : ℕ, realCpSaturatedBracket p k s) -
            ∑ k ∈ Finset.range M, realCpSaturatedBracket p k s)
        atTop (nhds 0) := by
    simpa using hconstant.sub hpartial
  have htail : ∀ M : ℕ,
      realCpBracketCutoffTail p M s =
        (∑' k : ℕ, realCpSaturatedBracket p k s) -
          ∑ k ∈ Finset.range M, realCpSaturatedBracket p k s := by
    intro M
    have hsplit := hsum.sum_add_tsum_nat_add M
    unfold realCpBracketCutoffTail
    linear_combination hsplit
  simpa only [htail] using hlimit

/-- Os cutoffs alinhados escapam para o infinito quando a outra base e positiva. -/
theorem crossPrimeAlignedCutoff_tendsto_atTop
    (other : ℕ) (hother : 0 < other) :
    Tendsto (fun L : ℕ ↦ crossPrimeAlignedCutoff other L)
      atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop b] with L hL
  have hotherOne : 1 ≤ other := hother
  have hmul : L ≤ other * L := by
    calc
      L = 1 * L := by simp
      _ ≤ other * L := Nat.mul_le_mul_right L hotherOne
  unfold crossPrimeAlignedCutoff
  omega

/--
Num zero Genuine, a diferenca entre as correcoes verticais das duas bases
alinhadas tende a zero: a unica diferenca finita era carregada pelas caudas,
que agora sao resolvidas no limite.
-/
theorem verticalCorrection_cross_prime_aligned_tendsto_zero_of_genuine_zero
    (p q : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
      (fun L : ℕ ↦
        CPFormal.Genuine.Cp.verticalCorrection p
            (crossPrimeAlignedCutoff q L) (dirichletTerm s) -
          CPFormal.Genuine.Cp.verticalCorrection q
            (crossPrimeAlignedCutoff p L) (dirichletTerm s))
      atTop (nhds 0) := by
  have hconv : -1 < s.re := by linarith [hs.1]
  have htailP :=
    (realCpBracketCutoffTail_tendsto_zero p hp hconv).comp
      (crossPrimeAlignedCutoff_tendsto_atTop q hq.pos)
  have htailQ :=
    (realCpBracketCutoffTail_tendsto_zero q hq hconv).comp
      (crossPrimeAlignedCutoff_tendsto_atTop p hp.pos)
  have htailDiff :
      Tendsto
        (fun L : ℕ ↦
          realCpBracketCutoffTail p (crossPrimeAlignedCutoff q L) s -
            realCpBracketCutoffTail q (crossPrimeAlignedCutoff p L) s)
        atTop (nhds 0) := by
    simpa [Function.comp_def] using htailP.sub htailQ
  have hpoint : ∀ L : ℕ,
      CPFormal.Genuine.Cp.verticalCorrection p
            (crossPrimeAlignedCutoff q L) (dirichletTerm s) -
          CPFormal.Genuine.Cp.verticalCorrection q
            (crossPrimeAlignedCutoff p L) (dirichletTerm s) =
        realCpBracketCutoffTail p (crossPrimeAlignedCutoff q L) s -
          realCpBracketCutoffTail q (crossPrimeAlignedCutoff p L) s := by
    intro L
    have hdefect :
        crossPrimeAlignedCutoffDefect p q L s = 0 := by
      rw [crossPrimeAlignedCutoffDefect_eq_factor_sub_mul_genuine
        p q L hp hpodd hq hqodd hs, hzero, mul_zero]
    unfold crossPrimeAlignedCutoffDefect at hdefect
    linear_combination hdefect
  exact htailDiff.congr'
    (Eventually.of_forall fun L ↦ (hpoint L).symm)

/-- A correcao vertical e o prefixo horizontal curto vestido pelo peso da base. -/
theorem verticalCorrection_dirichlet_eq_cpow_mul_prefix
    (p M : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    CPFormal.Genuine.Cp.verticalCorrection p M (dirichletTerm s) =
      (p : ℂ) ^ (1 - s) * positiveDirichletPrefix s M := by
  rw [CPFormal.Genuine.Cp.verticalCorrection_eq_p_mul_centerSum]
  exact p_mul_centerSum_dirichlet_eq_cpow_mul_prefix p hp M s

/--
Forma horizontal final: num zero Genuine, os dois prefixos finitos vestidos
pelas bases sincronizam ao longo de todos os horizontes cruzados.
-/
theorem weightedHorizontalPrefixes_cross_prime_aligned_tendsto_zero_of_genuine_zero
    (p q : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
      (fun L : ℕ ↦
        (p : ℂ) ^ (1 - s) *
            positiveDirichletPrefix s (crossPrimeAlignedCutoff q L) -
          (q : ℂ) ^ (1 - s) *
            positiveDirichletPrefix s (crossPrimeAlignedCutoff p L))
      atTop (nhds 0) := by
  have hvertical :=
    verticalCorrection_cross_prime_aligned_tendsto_zero_of_genuine_zero
      p q hp hpodd hq hqodd hs hzero
  have hfunctions :
      (fun L : ℕ ↦
        (p : ℂ) ^ (1 - s) *
            positiveDirichletPrefix s (crossPrimeAlignedCutoff q L) -
          (q : ℂ) ^ (1 - s) *
            positiveDirichletPrefix s (crossPrimeAlignedCutoff p L)) =
      (fun L : ℕ ↦
        CPFormal.Genuine.Cp.verticalCorrection p
            (crossPrimeAlignedCutoff q L) (dirichletTerm s) -
          CPFormal.Genuine.Cp.verticalCorrection q
            (crossPrimeAlignedCutoff p L) (dirichletTerm s)) := by
    funext L
    rw [verticalCorrection_dirichlet_eq_cpow_mul_prefix
        p (crossPrimeAlignedCutoff q L) hp s,
      verticalCorrection_dirichlet_eq_cpow_mul_prefix
        q (crossPrimeAlignedCutoff p L) hq s]
  rw [hfunctions]
  exact hvertical

end

end CPFormal.Analytic.Cp
