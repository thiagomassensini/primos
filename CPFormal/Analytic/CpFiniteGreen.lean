import CPFormal.Analytic.CpGenuineCompatibility

/-!
# Identidade Green finita para os gradientes Cp

Este modulo fecha apenas o bulk finito que antecede o certificado Green
infinito. Ha duas identidades independentes:

1. uma formula de Green discreta em qualquer anel comutativo, cujo bordo sao
   literalmente os dois endpoints;
2. a telescopagem de um bloco Cp de gradientes de Dirichlet, que produz o
   autovalor exato `p^(-s)` e fatora a forma de Green finita.

O arquivo nao identifica ainda o endpoint de fluxo com o traco do Genuine e
nao declara que o bordo infinito se anula. Essas sao as obrigacoes seguintes;
em particular, nenhum bordo e definido como um residual tautologico.
-/

open scoped BigOperators Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-- Soma telescopica abstrata de diferencas consecutivas. -/
theorem sum_range_forwardDifference
    {R : Type*} [CommRing R] (f : ℕ → R) (start length : ℕ) :
    (∑ r ∈ Finset.range length,
      (f (start + r + 1) - f (start + r))) =
        f (start + length) - f start := by
  induction length with
  | zero => simp
  | succ length ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [Nat.add_succ]
      ring

/-- Bulk da formula de Green discreta em um corte `0,...,M`. -/
def finiteGreenBulk
    {R : Type*} [CommRing R] (u v : ℕ → R) (M : ℕ) : R :=
  ∑ n ∈ Finset.range M,
    ((u (n + 1) - u n) * v (n + 1) +
      u n * (v (n + 1) - v n))

/-- Bordo verdadeiro do corte: endpoint externo menos endpoint inicial. -/
def finiteGreenBoundary
    {R : Type*} [CommRing R] (u v : ℕ → R) (M : ℕ) : R :=
  u M * v M - u 0 * v 0

/-- Identidade Green/Stokes finita: o bulk telescopa exatamente ao bordo. -/
theorem finiteGreenBulk_eq_boundary
    {R : Type*} [CommRing R] (u v : ℕ → R) (M : ℕ) :
    finiteGreenBulk u v M = finiteGreenBoundary u v M := by
  unfold finiteGreenBulk finiteGreenBoundary
  have hpoint : ∀ n : ℕ,
      (u (n + 1) - u n) * v (n + 1) +
          u n * (v (n + 1) - v n) =
        u (n + 1) * v (n + 1) - u n * v n := by
    intro n
    ring
  simp_rw [hpoint]
  simpa using
    (sum_range_forwardDifference (fun n ↦ u n * v n) 0 M)

/-- Monomio de Dirichlet restrito aos naturais. -/
def natDirichletTerm (s : ℂ) (n : ℕ) : ℂ :=
  dirichletTerm s (n : ℤ)

/-- Gradiente positivo entre os endpoints `n+1` e `n+2`. -/
def positiveDirichletGradient (s : ℂ) (n : ℕ) : ℂ :=
  natDirichletTerm s (n + 2) - natDirichletTerm s (n + 1)

/-- Soma dos `p` gradientes consecutivos no bloco que comeca em `p(n+1)`. -/
def cpBlockGradient (p : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  ∑ r ∈ Finset.range p,
    (natDirichletTerm s (p * (n + 1) + r + 1) -
      natDirichletTerm s (p * (n + 1) + r))

/-- Multiplicatividade do monomio em dois naturais. -/
theorem natDirichletTerm_mul
    (a b : ℕ) (s : ℂ) :
    natDirichletTerm s (a * b) =
      natDirichletTerm s a * natDirichletTerm s b := by
  simpa [natDirichletTerm, dirichletTerm] using
    (Complex.natCast_mul_natCast_cpow a b (-s))

/-!
Autovetor exato no nivel finito: somar os gradientes de um bloco Cp equivale
a aplicar o autovalor `p^(-s)` ao gradiente horizontal correspondente.
-/
theorem cpBlockGradient_eq_eigenvalue_mul
    (p : ℕ) (s : ℂ) (n : ℕ) :
    cpBlockGradient p s n =
      natDirichletTerm s p * positiveDirichletGradient s n := by
  unfold cpBlockGradient
  rw [sum_range_forwardDifference]
  have hend : p * (n + 1) + p = p * (n + 2) := by ring
  rw [hend, natDirichletTerm_mul, natDirichletTerm_mul]
  unfold positiveDirichletGradient
  ring

/-- Reflexao espectral usada na forma de Green. -/
def reflectedParameter (s : ℂ) : ℂ :=
  1 - (starRingEnd ℂ) s

/-- Pareamento refletido finito dos gradientes. -/
def finiteReflectedGradientPairing (M : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range M,
    (starRingEnd ℂ) (positiveDirichletGradient s n) *
      positiveDirichletGradient (reflectedParameter s) n

/-- Forma de Green finita produzida pelos dois blocos Cp refletidos. -/
def finiteCpGreenFlux (p M : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range M,
    ((starRingEnd ℂ) (cpBlockGradient p s n) *
        positiveDirichletGradient (reflectedParameter s) n -
      (starRingEnd ℂ) (positiveDirichletGradient s n) *
        cpBlockGradient p (reflectedParameter s) n)

/-!
Fatoracao exata do Wronskiano finito. O coeficiente e a diferenca dos dois
autovalores refletidos; nao existe termo de erro no bulk de blocos completos.
-/
theorem finiteCpGreenFlux_eq_eigenvalueDifference_mul_pairing
    (p M : ℕ) (s : ℂ) :
    finiteCpGreenFlux p M s =
      ((starRingEnd ℂ) (natDirichletTerm s p) -
          natDirichletTerm (reflectedParameter s) p) *
        finiteReflectedGradientPairing M s := by
  unfold finiteCpGreenFlux finiteReflectedGradientPairing
  calc
    (∑ n ∈ Finset.range M,
      ((starRingEnd ℂ) (cpBlockGradient p s n) *
          positiveDirichletGradient (reflectedParameter s) n -
        (starRingEnd ℂ) (positiveDirichletGradient s n) *
          cpBlockGradient p (reflectedParameter s) n)) =
        ∑ n ∈ Finset.range M,
          (((starRingEnd ℂ) (natDirichletTerm s p) -
              natDirichletTerm (reflectedParameter s) p) *
            ((starRingEnd ℂ) (positiveDirichletGradient s n) *
              positiveDirichletGradient (reflectedParameter s) n)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [cpBlockGradient_eq_eigenvalue_mul,
        cpBlockGradient_eq_eigenvalue_mul]
      simp only [map_mul]
      ring
    _ = ((starRingEnd ℂ) (natDirichletTerm s p) -
          natDirichletTerm (reflectedParameter s) p) *
        ∑ n ∈ Finset.range M,
          ((starRingEnd ℂ) (positiveDirichletGradient s n) *
            positiveDirichletGradient (reflectedParameter s) n) := by
      rw [Finset.mul_sum]

/-- Os mesmos cortes finitos convergem ao Genuine canonico no semiplano
inicial, depois de recolocar o fator da camera. -/
theorem finiteChart_dirichlet_tendsto_factor_mul_genuineContinuation
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto
      (fun M : ℕ ↦
        CPFormal.Genuine.Cp.finiteChart p M (dirichletTerm s))
      atTop
      (nhds (cpChartFactor p s * genuineContinuation s)) := by
  rw [genuineContinuation_eq_genuineDirichlet hs]
  simpa [cpChartFactor] using
    (finiteChart_dirichlet_tendsto_genuine_factor p hp hpodd hs)

end

end CPFormal.Analytic.Cp
