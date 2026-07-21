import CPFormal.Analytic.CpRealSpectralOperator
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Gerador espectral real finito e orbita unitaria Genuine-first

A geometria de carry fixa a amplitude critica. Este modulo separa rigorosamente
as duas funcoes que antes podiam ser confundidas na linguagem numerica:

* `finiteRealSpectralGenerator N` e o gerador diagonal com frequencias
  `log (n + 1)` no corte finito;
* `finiteRealSpectralEvolution N t` e a orbita unitaria gerada por essas
  frequencias;
* `IsRealSpectralResonance t` e o fechamento do readout Genuine ao longo da
  orbita.

Assim, `t` e o parametro real do grupo unitario. Os autovalores do gerador
finito sao `log (n + 1)`; as alturas detectadas pelo laboratorio sao
ressonancias do readout, nao autovalores desse operador diagonal.

Nenhuma tabela de alturas, zero, refinamento numerico ou hipotese Green entra
nas identidades abaixo.
-/

open scoped ComplexConjugate InnerProduct

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Espaco de Hilbert do corte espectral finito. -/
abbrev FiniteRealSpectralHilbert (N : ℕ) := EuclideanSpace ℂ (Fin N)

/-- Frequencia aritmetica do vertice positivo `n + 1`. -/
def finiteRealSpectralFrequency {N : ℕ} (n : Fin N) : ℝ :=
  Real.log (((n.1 + 1 : ℕ) : ℝ))

/-- Gerador diagonal finito `L_N |n> = log(n+1) |n>`. -/
noncomputable def finiteRealSpectralGenerator (N : ℕ) :
    FiniteRealSpectralHilbert N →ₗ[ℂ] FiniteRealSpectralHilbert N where
  toFun x := WithLp.toLp 2 fun n =>
    (finiteRealSpectralFrequency n : ℂ) * x n
  map_add' x y := by
    ext n
    simp [mul_add]
  map_smul' a x := by
    ext n
    simp [mul_left_comm]

@[simp] theorem finiteRealSpectralGenerator_apply
    (N : ℕ) (x : FiniteRealSpectralHilbert N) (n : Fin N) :
    finiteRealSpectralGenerator N x n =
      (finiteRealSpectralFrequency n : ℂ) * x n := rfl

/-- O gerador diagonal finito e simetrico porque suas frequencias sao reais. -/
theorem finiteRealSpectralGenerator_isSymmetric (N : ℕ) :
    (finiteRealSpectralGenerator N).IsSymmetric := by
  intro x y
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro n hn
  simp [finiteRealSpectralGenerator_apply, mul_assoc, mul_left_comm]

/-- Versao auto-adjunta e continua do gerador em cada corte finito. -/
noncomputable def finiteRealSpectralSelfAdjointGenerator (N : ℕ) :
    selfAdjoint
      (FiniteRealSpectralHilbert N →L[ℂ] FiniteRealSpectralHilbert N) :=
  (finiteRealSpectralGenerator_isSymmetric N).toSelfAdjoint

/-- Fase unitaria da frequencia `log(n+1)`. -/
def finiteRealSpectralPhase {N : ℕ} (t : ℝ) (n : Fin N) : ℂ :=
  Complex.exp
    (-(((t * finiteRealSpectralFrequency n : ℝ) : ℂ) * Complex.I))

@[simp] theorem finiteRealSpectralPhase_zero {N : ℕ} (n : Fin N) :
    finiteRealSpectralPhase 0 n = 1 := by
  simp [finiteRealSpectralPhase]

theorem finiteRealSpectralPhase_add {N : ℕ} (t u : ℝ) (n : Fin N) :
    finiteRealSpectralPhase (t + u) n =
      finiteRealSpectralPhase t n * finiteRealSpectralPhase u n := by
  unfold finiteRealSpectralPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp] theorem finiteRealSpectralPhase_neg_mul {N : ℕ} (t : ℝ) (n : Fin N) :
    finiteRealSpectralPhase (-t) n * finiteRealSpectralPhase t n = 1 := by
  rw [← finiteRealSpectralPhase_add]
  simp

@[simp] theorem finiteRealSpectralPhase_mul_neg {N : ℕ} (t : ℝ) (n : Fin N) :
    finiteRealSpectralPhase t n * finiteRealSpectralPhase (-t) n = 1 := by
  rw [mul_comm, finiteRealSpectralPhase_neg_mul]

@[simp] theorem conj_finiteRealSpectralPhase {N : ℕ} (t : ℝ) (n : Fin N) :
    (starRingEnd ℂ) (finiteRealSpectralPhase t n) =
      finiteRealSpectralPhase (-t) n := by
  unfold finiteRealSpectralPhase
  rw [← Complex.exp_conj]
  congr 1
  simp

/-- Equivalencia linear dada pela rotacao coordenada a coordenada. -/
noncomputable def finiteRealSpectralEvolutionLinearEquiv
    (N : ℕ) (t : ℝ) :
    FiniteRealSpectralHilbert N ≃ₗ[ℂ] FiniteRealSpectralHilbert N where
  toFun x := WithLp.toLp 2 fun n => finiteRealSpectralPhase t n * x n
  invFun x := WithLp.toLp 2 fun n => finiteRealSpectralPhase (-t) n * x n
  map_add' x y := by
    ext n
    simp [mul_add]
  map_smul' a x := by
    ext n
    simp [mul_left_comm]
  left_inv x := by
    ext n
    change finiteRealSpectralPhase (-t) n *
      (finiteRealSpectralPhase t n * x n) = x n
    rw [← mul_assoc, finiteRealSpectralPhase_neg_mul, one_mul]
  right_inv x := by
    ext n
    change finiteRealSpectralPhase t n *
      (finiteRealSpectralPhase (-t) n * x n) = x n
    rw [← mul_assoc, finiteRealSpectralPhase_mul_neg, one_mul]

@[simp] theorem finiteRealSpectralEvolutionLinearEquiv_apply
    (N : ℕ) (t : ℝ) (x : FiniteRealSpectralHilbert N) (n : Fin N) :
    finiteRealSpectralEvolutionLinearEquiv N t x n =
      finiteRealSpectralPhase t n * x n := rfl

/-- A evolucao finita preserva o produto interno, logo e unitaria. -/
noncomputable def finiteRealSpectralEvolution (N : ℕ) (t : ℝ) :
    FiniteRealSpectralHilbert N ≃ₗᵢ[ℂ] FiniteRealSpectralHilbert N :=
  (finiteRealSpectralEvolutionLinearEquiv N t).isometryOfInner (by
    intro x y
    rw [PiLp.inner_apply, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [finiteRealSpectralEvolutionLinearEquiv_apply,
      RCLike.inner_apply, map_mul, conj_finiteRealSpectralPhase]
    calc
      finiteRealSpectralPhase t n *
          (y n * (finiteRealSpectralPhase (-t) n * (starRingEnd ℂ) (x n))) =
        (finiteRealSpectralPhase t n * finiteRealSpectralPhase (-t) n) *
          (y n * (starRingEnd ℂ) (x n)) := by ring
      _ = y n * (starRingEnd ℂ) (x n) := by
        rw [finiteRealSpectralPhase_mul_neg, one_mul])

@[simp] theorem finiteRealSpectralEvolution_apply
    (N : ℕ) (t : ℝ) (x : FiniteRealSpectralHilbert N) (n : Fin N) :
    finiteRealSpectralEvolution N t x n =
      finiteRealSpectralPhase t n * x n := rfl

@[simp] theorem finiteRealSpectralEvolution_zero
    (N : ℕ) (x : FiniteRealSpectralHilbert N) :
    finiteRealSpectralEvolution N 0 x = x := by
  ext n
  simp

/-- Lei de grupo exata `U_(t+u) = U_t U_u`. -/
theorem finiteRealSpectralEvolution_add
    (N : ℕ) (t u : ℝ) (x : FiniteRealSpectralHilbert N) :
    finiteRealSpectralEvolution N (t + u) x =
      finiteRealSpectralEvolution N t
        (finiteRealSpectralEvolution N u x) := by
  ext n
  simp [finiteRealSpectralPhase_add, mul_assoc]

/-- Vetor canonico concentrado numa unica frequencia. -/
def finiteRealSpectralBasisVector (N : ℕ) (n : Fin N) :
    FiniteRealSpectralHilbert N :=
  PiLp.single 2 n 1

/-- Os autovalores do gerador finito sao as frequencias `log(n+1)`. -/
theorem finiteRealSpectralGenerator_basisVector
    (N : ℕ) (n : Fin N) :
    finiteRealSpectralGenerator N (finiteRealSpectralBasisVector N n) =
      (finiteRealSpectralFrequency n : ℂ) •
        finiteRealSpectralBasisVector N n := by
  ext m
  by_cases h : m = n
  · subst m
    simp [finiteRealSpectralBasisVector]
  · simp [finiteRealSpectralBasisVector, h]

/-- O estado real-espectral existente, agora empacotado no corte finito. -/
def finiteRealSpectralStateVector (N : ℕ) (t : ℝ) :
    FiniteRealSpectralHilbert N :=
  WithLp.toLp 2 fun n => realSpectralState t n.1

@[simp] theorem finiteRealSpectralStateVector_apply
    (N : ℕ) (t : ℝ) (n : Fin N) :
    finiteRealSpectralStateVector N t n = realSpectralState t n.1 := rfl

/-- Predicado intrinseco: uma ressonancia e um zero do readout Genuine ao
longo da orbita real critica. -/
def IsRealSpectralResonance (t : ℝ) : Prop :=
  realSpectralGenuine t = 0

/-- Qualquer camera prima impar reconhece exatamente as mesmas ressonancias. -/
theorem isRealSpectralResonance_iff_chart_zero
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) (t : ℝ) :
    IsRealSpectralResonance t ↔
      bracketedDirichletChart p (criticalLineParameter t) = 0 := by
  simpa [IsRealSpectralResonance] using
    (bracketedDirichletChart_criticalLine_zero_iff_realSpectralGenuine_zero
      p hp hpodd t).symm

end

end CPFormal.Analytic.Cp
