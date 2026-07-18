import CPFormal.Analytic.CpFiniteDirichletChart
import Mathlib.Analysis.PSeriesComplex

/-!
# Limite da carta Cp no semiplano de convergencia absoluta

Partimos da identidade finita ja verificada e tomamos `M -> infinity` apenas
sob a hipotese `1 < re(s)`. O objeto Genuine desta etapa e definido primeiro
pela propria serie de Dirichlet positiva, sem usar a zeta como definicao.

O resultado e

`finiteChart_p,M(s) -> (1 - p^(1-s)) * genuineDirichlet(s)`.

Este arquivo nao trata continuacao analitica, o dominio bracketado maior,
zeros ou a ponte Green.
-/

open scoped BigOperators Topology
open Filter

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Canal Genuine inicial: a serie positiva `sum_{n>=1} n^(-s)`. -/
def genuineDirichlet (s : ℂ) : ℂ :=
  ∑' k : ℕ, dirichletTerm s (((k + 1 : ℕ) : ℤ))

/-- No semiplano `re(s)>1`, os monomios positivos sao somaveis. -/
theorem summable_dirichletTerm_nat_add_one
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun k : ℕ =>
      dirichletTerm s (((k + 1 : ℕ) : ℤ))) := by
  have hbase : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
    Complex.summable_one_div_nat_cpow.mpr hs
  have hshift := hbase.comp_injective
    (show Function.Injective (fun n : ℕ => n + 1) by
      intro a b hab
      exact Nat.add_right_cancel hab)
  simpa [Function.comp_def, dirichletTerm, Complex.cpow_neg] using hshift

/-- Os prefixos positivos convergem para o canal Genuine inicial. -/
theorem positiveDirichletPrefix_tendsto_genuineDirichlet
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto (positiveDirichletPrefix s) atTop
      (nhds (genuineDirichlet s)) := by
  change Tendsto
    (fun N : ℕ => ∑ k ∈ Finset.range N,
      dirichletTerm s (((k + 1 : ℕ) : ℤ)))
    atTop
    (nhds (∑' k : ℕ,
      dirichletTerm s (((k + 1 : ℕ) : ℤ))))
  exact (summable_dirichletTerm_nat_add_one hs).tendsto_sum_tsum_nat

/-- Acrescentar um termo ao prefixo positivo. -/
theorem positiveDirichletPrefix_succ
    (s : ℂ) (N : ℕ) :
    positiveDirichletPrefix s (N + 1) =
      positiveDirichletPrefix s N +
        dirichletTerm s (((N + 1 : ℕ) : ℤ)) := by
  simp [positiveDirichletPrefix, Finset.sum_range_succ]

/-- O prefixo por `range` e a soma literal no intervalo inteiro `1,...,N`. -/
theorem positiveDirichletPrefix_eq_sum_Icc
    (s : ℂ) (N : ℕ) :
    positiveDirichletPrefix s N =
      ∑ n ∈ Finset.Icc (1 : ℤ) (N : ℤ), dirichletTerm s n := by
  induction N with
  | zero =>
      simp [positiveDirichletPrefix]
  | succ N ih =>
      rw [positiveDirichletPrefix_succ, ih]
      have hset :
          insert (((N + 1 : ℕ) : ℤ))
              (Finset.Icc (1 : ℤ) (N : ℤ)) =
            Finset.Icc (1 : ℤ) (((N + 1 : ℕ) : ℤ)) := by
        ext n
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      have hnot :
          (((N + 1 : ℕ) : ℤ)) ∉ Finset.Icc (1 : ℤ) (N : ℤ) := by
        simp only [Finset.mem_Icc]
        omega
      rw [← hset, Finset.sum_insert hnot]
      ring

/-- A carta finita usa dois prefixos da mesma serie Genuine. -/
theorem finiteChart_dirichlet_eq_two_prefixes
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (M : ℕ) (s : ℂ) :
    CPFormal.Genuine.Cp.finiteChart p M (dirichletTerm s) =
      positiveDirichletPrefix s
          (p * M + CPFormal.Genuine.Cp.halfRange p) -
        (p : ℂ) ^ (1 - s) * positiveDirichletPrefix s M := by
  rw [finiteChart_dirichlet_eq_prefix_sub_cpow_mul_prefix p hp hpodd M s]
  have hlong :
      (∑ n ∈ Finset.Icc (1 : ℤ)
        ((p : ℤ) * (M : ℤ) +
          (CPFormal.Genuine.Cp.halfRange p : ℤ)), dirichletTerm s n) =
        positiveDirichletPrefix s
          (p * M + CPFormal.Genuine.Cp.halfRange p) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using
      (positiveDirichletPrefix_eq_sum_Icc s
        (p * M + CPFormal.Genuine.Cp.halfRange p)).symm
  rw [hlong]

/-- O cutoff longo `p*M+halfRange(p)` tambem tende ao infinito. -/
theorem chartCutoff_tendsto_atTop
    (p : ℕ) (hp : Nat.Prime p) :
    Tendsto (fun M : ℕ =>
      p * M + CPFormal.Genuine.Cp.halfRange p) atTop atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro b
  filter_upwards [eventually_ge_atTop b] with a ha
  have hpone : 1 ≤ p := hp.one_le
  calc
    b ≤ a := ha
    _ ≤ p * a := by
      simpa only [one_mul] using Nat.mul_le_mul_right a hpone
    _ ≤ p * a + CPFormal.Genuine.Cp.halfRange p :=
      Nat.le_add_right _ _

/-!
Passagem ao limite principal. Os dois prefixos convergem para o mesmo canal;
a identidade finita e a continuidade das operacoes produzem o fator da carta.
-/
theorem finiteChart_dirichlet_tendsto_genuine_factor
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto
      (fun M : ℕ =>
        CPFormal.Genuine.Cp.finiteChart p M (dirichletTerm s))
      atTop
      (nhds ((1 - (p : ℂ) ^ (1 - s)) * genuineDirichlet s)) := by
  have hprefix := positiveDirichletPrefix_tendsto_genuineDirichlet hs
  have hlong :
      Tendsto
        (fun M : ℕ => positiveDirichletPrefix s
          (p * M + CPFormal.Genuine.Cp.halfRange p))
        atTop (nhds (genuineDirichlet s)) := by
    simpa [Function.comp_def] using
      hprefix.comp (chartCutoff_tendsto_atTop p hp)
  have hscaled :
      Tendsto
        (fun M : ℕ =>
          (p : ℂ) ^ (1 - s) * positiveDirichletPrefix s M)
        atTop
        (nhds ((p : ℂ) ^ (1 - s) * genuineDirichlet s)) := by
    exact tendsto_const_nhds.mul hprefix
  have hdiff := hlong.sub hscaled
  have heq :
      (fun M : ℕ =>
        positiveDirichletPrefix s
            (p * M + CPFormal.Genuine.Cp.halfRange p) -
          (p : ℂ) ^ (1 - s) * positiveDirichletPrefix s M) =ᶠ[atTop]
        (fun M : ℕ =>
          CPFormal.Genuine.Cp.finiteChart p M (dirichletTerm s)) :=
    Filter.Eventually.of_forall fun M =>
      (finiteChart_dirichlet_eq_two_prefixes p hp hpodd M s).symm
  have hchart := hdiff.congr' heq
  simpa only [sub_mul, one_mul] using hchart

end

end CPFormal.Analytic.Cp
