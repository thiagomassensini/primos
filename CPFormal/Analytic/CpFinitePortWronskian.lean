import CPFormal.Analytic.CpFiniteTfvdBridge

/-!
# Wronskiano finito: diagonal enriquecida e interferencia escalar

As portas TFVD preservam uma coordenada para cada bloco. Este arquivo prova
por que essa proveniencia precisa sobreviver ate o pareamento de Green.

O Wronskiano de duas sinteses escalares e uma soma sobre todos os pares de
blocos `(m,n)`. Sua parte diagonal `m=n` e o pareamento ortogonal natural; a
parte `m!=n` e interferencia introduzida pela sintese escalar. A decomposicao
abaixo e explicita: o termo off-diagonal nao e definido como um residual.

Um witness em dois blocos prova que a interferencia nao desaparece por uma
identidade algebrica universal. Portanto nao e legitimo identificar o
Wronskiano das somas escalares `Phi_M/Psi_M` diretamente com o fluxo Green
diagonal. A proxima ponte deve parear as coordenadas TFVD primeiro e somente
depois sintetizar.
-/

open scoped BigOperators

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Sintese escalar de uma familia ate o corte `M`. -/
def finitePortSynthesis (M : ℕ) (f : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Finset.range M, f m

/-- Entrada `(m,n)` da forma de Wronski refletida entre quatro familias. -/
def finitePortWedgeEntry
    (phi psi phiSharp psiSharp : ℕ → ℂ) (m n : ℕ) : ℂ :=
  (starRingEnd ℂ) (psi m) * phiSharp n -
    (starRingEnd ℂ) (phi m) * psiSharp n

/-- Wronskiano formado depois de comprimir cada porta a um escalar. -/
def finiteScalarPortWronskian
    (M : ℕ) (phi psi phiSharp psiSharp : ℕ → ℂ) : ℂ :=
  (starRingEnd ℂ) (finitePortSynthesis M psi) *
      finitePortSynthesis M phiSharp -
    (starRingEnd ℂ) (finitePortSynthesis M phi) *
      finitePortSynthesis M psiSharp

/-- Matriz completa do Wronskiano antes de separar registros ortogonais. -/
def finiteFullPortWronskian
    (M : ℕ) (phi psi phiSharp psiSharp : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Finset.range M,
    ∑ n ∈ Finset.range M,
      finitePortWedgeEntry phi psi phiSharp psiSharp m n

/-- Parte diagonal: cada bloco e pareado somente com o mesmo registro. -/
def finiteDiagonalPortWronskian
    (M : ℕ) (phi psi phiSharp psiSharp : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Finset.range M,
    ∑ n ∈ Finset.range M,
      if m = n then
        finitePortWedgeEntry phi psi phiSharp psiSharp m n
      else 0

/-- Interferencia explicita entre registros distintos. -/
def finiteOffDiagonalPortWronskian
    (M : ℕ) (phi psi phiSharp psiSharp : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Finset.range M,
    ∑ n ∈ Finset.range M,
      if m = n then 0
      else finitePortWedgeEntry phi psi phiSharp psiSharp m n

/-- Distribuir as duas sinteses escalares produz a matriz completa. -/
theorem finiteScalarPortWronskian_eq_full
    (M : ℕ) (phi psi phiSharp psiSharp : ℕ → ℂ) :
    finiteScalarPortWronskian M phi psi phiSharp psiSharp =
      finiteFullPortWronskian M phi psi phiSharp psiSharp := by
  unfold finiteScalarPortWronskian finiteFullPortWronskian
    finitePortSynthesis finitePortWedgeEntry
  simp only [map_sum]
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]

/-- A matriz completa separa exatamente diagonal e off-diagonal. -/
theorem finiteFullPortWronskian_eq_diagonal_add_offDiagonal
    (M : ℕ) (phi psi phiSharp psiSharp : ℕ → ℂ) :
    finiteFullPortWronskian M phi psi phiSharp psiSharp =
      finiteDiagonalPortWronskian M phi psi phiSharp psiSharp +
        finiteOffDiagonalPortWronskian M phi psi phiSharp psiSharp := by
  unfold finiteFullPortWronskian finiteDiagonalPortWronskian
    finiteOffDiagonalPortWronskian
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hmn : m = n
  · simp [hmn]
  · simp [hmn]

/-!
Identidade central do checkpoint. A igualdade desejada entre a compressao
escalar e um Green diagonal exige, alem da identificacao coordenada a
coordenada, a anulacao do termo off-diagonal.
-/
theorem finiteScalarPortWronskian_eq_diagonal_add_offDiagonal
    (M : ℕ) (phi psi phiSharp psiSharp : ℕ → ℂ) :
    finiteScalarPortWronskian M phi psi phiSharp psiSharp =
      finiteDiagonalPortWronskian M phi psi phiSharp psiSharp +
        finiteOffDiagonalPortWronskian M phi psi phiSharp psiSharp := by
  rw [finiteScalarPortWronskian_eq_full,
    finiteFullPortWronskian_eq_diagonal_add_offDiagonal]

/-- Witness de dois blocos: a interferencia off-diagonal pode ser `1`. -/
theorem finiteOffDiagonalPortWronskian_two_witness :
    finiteOffDiagonalPortWronskian 2
      (fun _ ↦ 0)
      (fun m ↦ if m = 0 then 1 else 0)
      (fun n ↦ if n = 1 then 1 else 0)
      (fun _ ↦ 0) = 1 := by
  norm_num [finiteOffDiagonalPortWronskian, finitePortWedgeEntry,
    Finset.sum_range_succ]

/-- Logo a sintese escalar nao coincide universalmente com a diagonal. -/
theorem finiteScalarPortWronskian_ne_diagonal_witness :
    finiteScalarPortWronskian 2
        (fun _ ↦ 0)
        (fun m ↦ if m = 0 then 1 else 0)
        (fun n ↦ if n = 1 then 1 else 0)
        (fun _ ↦ 0) ≠
      finiteDiagonalPortWronskian 2
        (fun _ ↦ 0)
        (fun m ↦ if m = 0 then 1 else 0)
        (fun n ↦ if n = 1 then 1 else 0)
        (fun _ ↦ 0) := by
  norm_num [finiteScalarPortWronskian, finitePortSynthesis,
    finiteDiagonalPortWronskian, finitePortWedgeEntry,
    Finset.sum_range_succ]

end

end CPFormal.Analytic.Cp
