import CPFormal.Genuine.CpFiniteChart

/-!
# Fatoracao finita da carta Cp em potencias de Dirichlet

Este arquivo faz somente a primeira especializacao analitica indispensavel.
Para inteiros positivos, usamos a potencia complexa principal `n ^ (-s)`.
A positividade das bases permite aplicar a multiplicatividade de `cpow` sem
qualquer ambiguidade de ramo.

O resultado central e inteiramente finito:

`p * sum_{m=1}^M (p*m)^(-s) = p^(1-s) * sum_{m=1}^M m^(-s)`.

Nao ha serie infinita, convergencia, zeta, continuacao analitica ou zeros.
-/

open scoped BigOperators

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Monomio de Dirichlet no ramo principal; a carta o usa apenas em `n > 0`. -/
def dirichletTerm (s : ℂ) (n : ℤ) : ℂ :=
  (n : ℂ) ^ (-s)

/-- Prefixo `1^(-s) + ... + M^(-s)` escrito com indices iniciando em zero. -/
def positiveDirichletPrefix (s : ℂ) (M : ℕ) : ℂ :=
  ∑ k ∈ Finset.range M, dirichletTerm s (((k + 1 : ℕ) : ℤ))

/-- Em um centro alinhado, o monomio separa base prima e indice horizontal. -/
theorem dirichletTerm_alignedCenter
    (p k : ℕ) (s : ℂ) :
    dirichletTerm s (CPFormal.Genuine.Cp.alignedCenter p k) =
      dirichletTerm s (p : ℤ) *
        dirichletTerm s (((k + 1 : ℕ) : ℤ)) := by
  simpa [dirichletTerm, CPFormal.Genuine.Cp.alignedCenter] using
    (Complex.natCast_mul_natCast_cpow p (k + 1) (-s))

/-- O coeficiente `p` junto de `p^(-s)` e exatamente `p^(1-s)`. -/
theorem prime_mul_dirichletTerm_eq_cpow_one_sub
    (p : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    (p : ℂ) * dirichletTerm s (p : ℤ) =
      (p : ℂ) ^ (1 - s) := by
  have hp0 : (p : ℂ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  simpa [dirichletTerm, sub_eq_add_neg] using
    (Complex.cpow_add (x := (p : ℂ)) (1 : ℂ) (-s) hp0).symm

/-!
Coracao desta etapa: a correcao vertical finita se separa em um fator da base
e o prefixo horizontal curto.
-/
theorem p_mul_centerSum_dirichlet_eq_cpow_mul_prefix
    (p : ℕ) (hp : Nat.Prime p) (M : ℕ) (s : ℂ) :
    (p : ℂ) *
        ∑ k ∈ Finset.range M,
          dirichletTerm s (CPFormal.Genuine.Cp.alignedCenter p k) =
      (p : ℂ) ^ (1 - s) * positiveDirichletPrefix s M := by
  unfold positiveDirichletPrefix
  simp_rw [dirichletTerm_alignedCenter]
  rw [← Finset.mul_sum]
  rw [← mul_assoc]
  rw [prime_mul_dirichletTerm_eq_cpow_one_sub p hp s]

/-- Carta Cp finita: prefixo positivo longo menos o prefixo vertical fatorado. -/
theorem finiteChart_dirichlet_eq_prefix_sub_cpow_mul_prefix
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (M : ℕ) (s : ℂ) :
    CPFormal.Genuine.Cp.finiteChart p M (dirichletTerm s) =
      (∑ n ∈ Finset.Icc (1 : ℤ)
        ((p : ℤ) * (M : ℤ) +
          (CPFormal.Genuine.Cp.halfRange p : ℤ)), dirichletTerm s n) -
        (p : ℂ) ^ (1 - s) * positiveDirichletPrefix s M := by
  rw [CPFormal.Genuine.Cp.finiteChart_eq_positiveIntervalSum_sub_p_mul_centerSum
    p hp hpodd]
  rw [p_mul_centerSum_dirichlet_eq_cpow_mul_prefix p hp M s]

end

end CPFormal.Analytic.Cp
