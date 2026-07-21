import CPFormal.Analytic.CpRealSpectralGenerator
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Gerador espectral real maximal em l2

Este modulo passa do corte finito para o espaco de Hilbert

  H = l2(N, C)

e define o operador maximal de multiplicacao

  (L x)(n) = log(n+1) x(n)

no dominio exato em que o lado direito pertence novamente a l2. O dominio
contem a base canonica e e denso. O adjunto e calculado coordenada por
coordenada contra essa base, o que prova que o dominio maximal e
auto-adjunto; em particular, seu grafo e fechado.

A segunda metade constroi a orbita unitaria diagonal

  (U_t x)(n) = exp(-i t log(n+1)) x(n)

com identidade, inversa e lei de grupo exatas. As alturas Genuine continuam
sendo ressonancias do readout ao longo dessa orbita, e nao autovalores de L.

Nenhuma tabela de zeros, resultado numerico, funcao zeta ou hipotese Green
entra nas provas abaixo.
-/

open scoped ComplexConjugate InnerProduct ENNReal Topology

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Espaco de Hilbert espectral infinito. -/
abbrev InfiniteRealSpectralHilbert := ℓ²(ℕ, ℂ)

/-- Frequencia aritmetica da coordenada `n`: `log(n+1)`. -/
def infiniteRealSpectralFrequency (n : ℕ) : ℝ :=
  Real.log (((n + 1 : ℕ) : ℝ))

/-- Dominio maximal do multiplicador por `log(n+1)`. -/
def infiniteRealSpectralMaximalDomain :
    Submodule ℂ InfiniteRealSpectralHilbert where
  carrier :=
    {x | Memℓp (fun n => (infiniteRealSpectralFrequency n : ℂ) * x n) 2}
  zero_mem' := by
    simpa using (zero_memℓp : Memℓp (0 : ℕ → ℂ) 2)
  add_mem' x y hx hy := by
    simpa [mul_add] using hx.add hy
  smul_mem' c x hx := by
    simpa [mul_assoc, mul_left_comm] using hx.const_smul c

/-- Operador maximal `L x(n) = log(n+1) x(n)` em `l2`. -/
def infiniteRealSpectralGenerator :
    InfiniteRealSpectralHilbert →ₗ.[ℂ] InfiniteRealSpectralHilbert where
  domain := infiniteRealSpectralMaximalDomain
  toFun :=
    { toFun := fun x =>
        ⟨fun n => (infiniteRealSpectralFrequency n : ℂ) * x n, x.2⟩
      map_add' := by
        intro x y
        ext n
        simp [mul_add]
      map_smul' := by
        intro c x
        ext n
        simp [mul_assoc, mul_left_comm] }

@[simp] theorem infiniteRealSpectralGenerator_apply
    (x : infiniteRealSpectralGenerator.domain) (n : ℕ) :
    infiniteRealSpectralGenerator x n =
      (infiniteRealSpectralFrequency n : ℂ) * x n := rfl

@[simp] theorem mem_infiniteRealSpectralGenerator_domain
    (x : InfiniteRealSpectralHilbert) :
    x ∈ infiniteRealSpectralGenerator.domain ↔
      Memℓp (fun n => (infiniteRealSpectralFrequency n : ℂ) * x n) 2 :=
  Iff.rfl

/-- Vetor canonico concentrado numa unica frequencia. -/
def infiniteRealSpectralBasisVector (n : ℕ) :
    InfiniteRealSpectralHilbert :=
  lp.single 2 n 1

/-- Todo vetor canonico pertence ao dominio maximal. -/
theorem infiniteRealSpectralBasisVector_mem_domain (n : ℕ) :
    infiniteRealSpectralBasisVector n ∈ infiniteRealSpectralGenerator.domain := by
  change Memℓp
    (fun m => (infiniteRealSpectralFrequency m : ℂ) *
      infiniteRealSpectralBasisVector n m) 2
  let v : InfiniteRealSpectralHilbert :=
    lp.single 2 n (infiniteRealSpectralFrequency n : ℂ)
  have hfun :
      (fun m => (infiniteRealSpectralFrequency m : ℂ) *
        infiniteRealSpectralBasisVector n m) =
        fun m => v m := by
    funext m
    by_cases h : m = n
    · subst m
      simp [v, infiniteRealSpectralBasisVector]
    · simp [v, infiniteRealSpectralBasisVector, h]
  rw [hfun]
  exact v.2

/-- A base canonica diagonaliza o gerador maximal. -/
theorem infiniteRealSpectralGenerator_basisVector (n : ℕ) :
    infiniteRealSpectralGenerator
      ⟨infiniteRealSpectralBasisVector n,
        infiniteRealSpectralBasisVector_mem_domain n⟩ =
      (infiniteRealSpectralFrequency n : ℂ) •
        infiniteRealSpectralBasisVector n := by
  ext m
  by_cases h : m = n
  · subst m
    simp [infiniteRealSpectralBasisVector]
  · simp [infiniteRealSpectralBasisVector, h]

/-- Base de Hilbert canonica de `l2(N,C)`. -/
def infiniteRealSpectralHilbertBasis :
    HilbertBasis ℕ ℂ InfiniteRealSpectralHilbert :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

@[simp] theorem infiniteRealSpectralHilbertBasis_apply (n : ℕ) :
    infiniteRealSpectralHilbertBasis n =
      infiniteRealSpectralBasisVector n := rfl

/-- O dominio maximal e denso porque contem a base canonica. -/
theorem infiniteRealSpectralGenerator_dense_domain :
    Dense (infiniteRealSpectralGenerator.domain :
      Set InfiniteRealSpectralHilbert) := by
  let b := infiniteRealSpectralHilbertBasis
  have hspan :
      Submodule.span ℂ (Set.range b) ≤
        infiniteRealSpectralGenerator.domain := by
    rw [Submodule.span_le]
    rintro x ⟨n, rfl⟩
    simpa [b] using infiniteRealSpectralBasisVector_mem_domain n
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply le_antisymm le_top
  calc
    (⊤ : Submodule ℂ InfiniteRealSpectralHilbert) =
        (Submodule.span ℂ (Set.range b)).topologicalClosure :=
      b.dense_span.symm
    _ ≤ infiniteRealSpectralGenerator.domain.topologicalClosure :=
      Submodule.topologicalClosure_mono hspan

/-- O multiplicador real e formalmente simetrico no dominio maximal. -/
theorem infiniteRealSpectralGenerator_isFormalAdjoint :
    infiniteRealSpectralGenerator.IsFormalAdjoint
      infiniteRealSpectralGenerator := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp [infiniteRealSpectralGenerator_apply, RCLike.inner_apply,
    mul_assoc, mul_left_comm, mul_comm]

/-- O adjunto age pela mesma formula coordenada a coordenada. -/
theorem infiniteRealSpectralGenerator_adjoint_apply
    (y : infiniteRealSpectralGenerator.adjoint.domain) (n : ℕ) :
    infiniteRealSpectralGenerator.adjoint y n =
      (infiniteRealSpectralFrequency n : ℂ) * y n := by
  have h :=
    (LinearPMap.adjoint_isFormalAdjoint
      (T := infiniteRealSpectralGenerator)
      infiniteRealSpectralGenerator_dense_domain).symm
      ⟨infiniteRealSpectralBasisVector n,
        infiniteRealSpectralBasisVector_mem_domain n⟩ y
  change
    inner ℂ
      (infiniteRealSpectralGenerator
        ⟨infiniteRealSpectralBasisVector n,
          infiniteRealSpectralBasisVector_mem_domain n⟩)
      (y : InfiniteRealSpectralHilbert) =
    inner ℂ (infiniteRealSpectralBasisVector n)
      (infiniteRealSpectralGenerator.adjoint y) at h
  rw [infiniteRealSpectralGenerator_basisVector] at h
  simpa [infiniteRealSpectralBasisVector, lp.inner_single_left] using h.symm

/-- A maximalidade: o dominio do adjunto ja pertence ao dominio original. -/
theorem infiniteRealSpectralGenerator_adjoint_domain_le :
    infiniteRealSpectralGenerator.adjoint.domain ≤
      infiniteRealSpectralGenerator.domain := by
  intro y hy
  change Memℓp
    (fun n => (infiniteRealSpectralFrequency n : ℂ) * y n) 2
  let z : InfiniteRealSpectralHilbert :=
    infiniteRealSpectralGenerator.adjoint ⟨y, hy⟩
  have hfun :
      (fun n => (infiniteRealSpectralFrequency n : ℂ) * y n) =
        fun n => z n := by
    funext n
    exact (infiniteRealSpectralGenerator_adjoint_apply ⟨y, hy⟩ n).symm
  rw [hfun]
  exact z.2

/-- O multiplicador maximal por `log(n+1)` e auto-adjunto. -/
theorem infiniteRealSpectralGenerator_isSelfAdjoint :
    IsSelfAdjoint infiniteRealSpectralGenerator := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · refine ⟨infiniteRealSpectralGenerator_adjoint_domain_le, ?_⟩
    intro x y hxy
    ext n
    rw [infiniteRealSpectralGenerator_adjoint_apply,
      infiniteRealSpectralGenerator_apply]
    exact congrArg
      (fun z : InfiniteRealSpectralHilbert =>
        (infiniteRealSpectralFrequency n : ℂ) * z n) hxy
  · exact
      infiniteRealSpectralGenerator_isFormalAdjoint.le_adjoint
        infiniteRealSpectralGenerator_dense_domain

/-- Em particular, o grafo do gerador maximal e fechado. -/
theorem infiniteRealSpectralGenerator_isClosed :
    infiniteRealSpectralGenerator.IsClosed :=
  infiniteRealSpectralGenerator_isSelfAdjoint.isClosed

/-- Fase unitaria da coordenada `n`. -/
def infiniteRealSpectralPhase (t : ℝ) (n : ℕ) : ℂ :=
  Complex.exp
    (-(((t * infiniteRealSpectralFrequency n : ℝ) : ℂ) * Complex.I))

@[simp] theorem infiniteRealSpectralPhase_zero (n : ℕ) :
    infiniteRealSpectralPhase 0 n = 1 := by
  simp [infiniteRealSpectralPhase]

theorem infiniteRealSpectralPhase_add (t u : ℝ) (n : ℕ) :
    infiniteRealSpectralPhase (t + u) n =
      infiniteRealSpectralPhase t n * infiniteRealSpectralPhase u n := by
  unfold infiniteRealSpectralPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp] theorem infiniteRealSpectralPhase_neg_mul (t : ℝ) (n : ℕ) :
    infiniteRealSpectralPhase (-t) n *
      infiniteRealSpectralPhase t n = 1 := by
  rw [← infiniteRealSpectralPhase_add]
  simp

@[simp] theorem infiniteRealSpectralPhase_mul_neg (t : ℝ) (n : ℕ) :
    infiniteRealSpectralPhase t n *
      infiniteRealSpectralPhase (-t) n = 1 := by
  rw [mul_comm, infiniteRealSpectralPhase_neg_mul]

@[simp] theorem conj_infiniteRealSpectralPhase (t : ℝ) (n : ℕ) :
    (starRingEnd ℂ) (infiniteRealSpectralPhase t n) =
      infiniteRealSpectralPhase (-t) n := by
  unfold infiniteRealSpectralPhase
  rw [← Complex.exp_conj]
  congr 1
  simp

@[simp] theorem norm_infiniteRealSpectralPhase (t : ℝ) (n : ℕ) :
    ‖infiniteRealSpectralPhase t n‖ = 1 := by
  rw [Complex.norm_exp]
  simp [infiniteRealSpectralPhase]

/-- Multiplicar por uma fase coordenada preserva a condicao `l2`. -/
theorem infiniteRealSpectralPhase_mul_memℓp
    (t : ℝ) (x : InfiniteRealSpectralHilbert) :
    Memℓp (fun n => infiniteRealSpectralPhase t n * x n) 2 := by
  exact x.2.mono' fun n => by
    rw [norm_mul, norm_infiniteRealSpectralPhase, one_mul]

/-- Equivalencia linear diagonal `U_t`, com inversa `U_-t`. -/
noncomputable def infiniteRealSpectralEvolutionLinearEquiv (t : ℝ) :
    InfiniteRealSpectralHilbert ≃ₗ[ℂ] InfiniteRealSpectralHilbert where
  toFun x :=
    ⟨fun n => infiniteRealSpectralPhase t n * x n,
      infiniteRealSpectralPhase_mul_memℓp t x⟩
  invFun x :=
    ⟨fun n => infiniteRealSpectralPhase (-t) n * x n,
      infiniteRealSpectralPhase_mul_memℓp (-t) x⟩
  map_add' x y := by
    ext n
    simp [mul_add]
  map_smul' c x := by
    ext n
    simp [mul_assoc, mul_left_comm]
  left_inv x := by
    ext n
    change infiniteRealSpectralPhase (-t) n *
      (infiniteRealSpectralPhase t n * x n) = x n
    rw [← mul_assoc, infiniteRealSpectralPhase_neg_mul, one_mul]
  right_inv x := by
    ext n
    change infiniteRealSpectralPhase t n *
      (infiniteRealSpectralPhase (-t) n * x n) = x n
    rw [← mul_assoc, infiniteRealSpectralPhase_mul_neg, one_mul]

@[simp] theorem infiniteRealSpectralEvolutionLinearEquiv_apply
    (t : ℝ) (x : InfiniteRealSpectralHilbert) (n : ℕ) :
    infiniteRealSpectralEvolutionLinearEquiv t x n =
      infiniteRealSpectralPhase t n * x n := rfl

/-- A orbita infinita preserva o produto interno, logo e unitaria. -/
noncomputable def infiniteRealSpectralEvolution (t : ℝ) :
    InfiniteRealSpectralHilbert ≃ₗᵢ[ℂ] InfiniteRealSpectralHilbert :=
  (infiniteRealSpectralEvolutionLinearEquiv t).isometryOfInner (by
    intro x y
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    apply tsum_congr
    intro n
    simp only [infiniteRealSpectralEvolutionLinearEquiv_apply,
      RCLike.inner_apply, map_mul, conj_infiniteRealSpectralPhase]
    calc
      infiniteRealSpectralPhase t n * y n *
          (infiniteRealSpectralPhase (-t) n *
            (starRingEnd ℂ) (x n)) =
        (infiniteRealSpectralPhase t n *
          infiniteRealSpectralPhase (-t) n) *
            (y n * (starRingEnd ℂ) (x n)) := by ring
      _ = y n * (starRingEnd ℂ) (x n) := by
        rw [infiniteRealSpectralPhase_mul_neg, one_mul])

@[simp] theorem infiniteRealSpectralEvolution_apply
    (t : ℝ) (x : InfiniteRealSpectralHilbert) (n : ℕ) :
    infiniteRealSpectralEvolution t x n =
      infiniteRealSpectralPhase t n * x n := rfl

@[simp] theorem infiniteRealSpectralEvolution_zero
    (x : InfiniteRealSpectralHilbert) :
    infiniteRealSpectralEvolution 0 x = x := by
  ext n
  simp

/-- Lei de grupo exata `U_(t+u)=U_t U_u`. -/
theorem infiniteRealSpectralEvolution_add
    (t u : ℝ) (x : InfiniteRealSpectralHilbert) :
    infiniteRealSpectralEvolution (t + u) x =
      infiniteRealSpectralEvolution t
        (infiniteRealSpectralEvolution u x) := by
  ext n
  simp [infiniteRealSpectralPhase_add, mul_assoc]

/-- `U_-t` e a inversa de `U_t`. -/
theorem infiniteRealSpectralEvolution_neg
    (t : ℝ) (x : InfiniteRealSpectralHilbert) :
    infiniteRealSpectralEvolution (-t)
        (infiniteRealSpectralEvolution t x) = x := by
  rw [← infiniteRealSpectralEvolution_add]
  simp

/-- O grupo unitario preserva exatamente a norma. -/
@[simp] theorem infiniteRealSpectralEvolution_norm
    (t : ℝ) (x : InfiniteRealSpectralHilbert) :
    ‖infiniteRealSpectralEvolution t x‖ = ‖x‖ :=
  (infiniteRealSpectralEvolution t).norm_map x

end

end CPFormal.Analytic.Cp
