import CPFormal.Analytic.CpFiniteGreen

/-!
# Endpoint refletido da identidade Green Cp

Este modulo isola o unico pedaco do bordo que decai apenas por aritmetica.
Para `s# = 1 - conj(s)`, o produto dos dois valores refletidos no endpoint
positivo `M+1` e exatamente `(M+1)⁻¹`; portanto o endpoint externo tende a
zero sem qualquer hipotese de fechamento.

Isso nao elimina o endpoint inicial da formula de Green. A identificacao e o
cancelamento desse endpoint com o traco bracketado permanecem uma obrigacao
separada, evitando transformar o bordo completo numa definicao tautologica.
-/

open scoped Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-- Valor de Dirichlet no `n`-esimo vertice positivo, isto e, em `n+1`. -/
def positiveDirichletValue (s : ℂ) (n : ℕ) : ℂ :=
  ((n + 1 : ℕ) : ℂ) ^ (-s)

/-- A versao positiva coincide com o monomio inteiro usado pelas cartas. -/
theorem positiveDirichletValue_eq_natDirichletTerm
    (s : ℂ) (n : ℕ) :
    positiveDirichletValue s n = natDirichletTerm s (n + 1) := by
  simp [positiveDirichletValue, natDirichletTerm, dirichletTerm]

/-- Produto refletido no endpoint externo do corte `0,...,M`. -/
def finiteReflectedOuterEndpoint (M : ℕ) (s : ℂ) : ℂ :=
  (starRingEnd ℂ) (positiveDirichletValue s M) *
    positiveDirichletValue (reflectedParameter s) M

/-- A reflexao `s# = 1-conj(s)` faz o produto de endpoint virar `1/(M+1)`. -/
theorem finiteReflectedOuterEndpoint_eq_inv
    (M : ℕ) (s : ℂ) :
    finiteReflectedOuterEndpoint M s = (((M + 1 : ℕ) : ℂ))⁻¹ := by
  let x : ℂ := ((M + 1 : ℕ) : ℂ)
  have hx : x ≠ 0 := by
    simp [x]
  have harg : x.arg ≠ Real.pi := by
    simp [x, Real.pi_ne_zero]
  have hxconj : Complex.conj x = x := by
    simp [x]
  have hconj :
      Complex.conj (x ^ (-s)) = x ^ (-Complex.conj s) := by
    have h := (Complex.cpow_conj x (-s) harg).symm
    rw [hxconj] at h
    simpa using h
  unfold finiteReflectedOuterEndpoint positiveDirichletValue reflectedParameter
  change
    Complex.conj (x ^ (-s)) * x ^ (-(1 - Complex.conj s)) = x⁻¹
  rw [hconj, ← Complex.cpow_add _ _ hx]
  have hexponent :
      -Complex.conj s + -(1 - Complex.conj s) = (-1 : ℂ) := by
    ring
  rw [hexponent, Complex.cpow_neg_one]

/-- O endpoint externo refletido desaparece no limite. -/
theorem finiteReflectedOuterEndpoint_tendsto_zero (s : ℂ) :
    Tendsto (fun M : ℕ ↦ finiteReflectedOuterEndpoint M s)
      atTop (nhds 0) := by
  have hinv :
      Tendsto (fun M : ℕ ↦ (((M + 1 : ℕ) : ℂ))⁻¹)
        atTop (nhds 0) := by
    exact (tendsto_add_atTop_iff_nat 1).2
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ))
  simpa only [finiteReflectedOuterEndpoint_eq_inv] using hinv

end

end CPFormal.Analytic.Cp
