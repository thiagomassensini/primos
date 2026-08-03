import CPFormal.Carry.CpMultibaseCameraAtlas
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The multibase camera atlas as a direct sum of vertical lines

Realizing each prime camera as an independent coordinate axis of the free real
space `ℕ →₀ ℝ`, the quantity `n` becomes the vector `∑_q v_q(n) · e_q`
(`factorizationVector`).  The camera `p` resolves the axis `V_p = ℝ·e_p`
(`cameraVerticalLine`); everything it leaves horizontal lives in
`H_p = span {e_q : q ≠ p}` (`cameraHorizontalSpace`), which is exactly the span
of the *other* cameras' vertical axes.

The main structural theorem is that these are complementary,
`IsCompl (cameraVerticalLine p) (cameraHorizontalSpace p)`: the atlas is a clean
internal direct sum, so "horizontal in `p`" is precisely the algebraic span of the
other verticals.  The linear functional `e_q ↦ log q` recovers the scalar log
decomposition of the companion module.

At this stage `CameraLogSpace` is the free finite-support real vector space.  No
topology, inner product, Hilbert completion or Bessel completeness is asserted
by the direct-sum theorem below.
-/

open Finsupp

namespace CPFormal.Carry.Cp

/-- The camera-log space: the free real space with one axis per camera. -/
abbrev CameraLogSpace := ℕ →₀ ℝ

/-- The vertical axis (unit direction) of camera `q`. -/
noncomputable def cameraAxis (q : ℕ) : CameraLogSpace := Finsupp.single q 1

/-- The vertical line resolved by camera `p`: the axis `ℝ·e_p`. -/
def cameraVerticalLine (p : ℕ) : Submodule ℝ CameraLogSpace :=
  Finsupp.supported ℝ ℝ ({p} : Set ℕ)

/-- The horizontal subspace left by camera `p`: the span of the other axes. -/
def cameraHorizontalSpace (p : ℕ) : Submodule ℝ CameraLogSpace :=
  Finsupp.supported ℝ ℝ ({p}ᶜ : Set ℕ)

/-- The quantity `n` as the vector `∑_q v_q(n) · e_q`. -/
noncomputable def factorizationVector (n : ℕ) : CameraLogSpace :=
  Finsupp.mapRange (Nat.cast : ℕ → ℝ) Nat.cast_zero (n.factorization)

@[simp] theorem factorizationVector_apply (n q : ℕ) :
    factorizationVector n q = (n.factorization q : ℝ) := by
  rw [factorizationVector, Finsupp.mapRange_apply]

/-- The vertical line is the span of the `p`-axis. -/
theorem cameraVerticalLine_eq_span (p : ℕ) :
    cameraVerticalLine p = Submodule.span ℝ (cameraAxis '' ({p} : Set ℕ)) := by
  rw [cameraVerticalLine, Finsupp.supported_eq_span_single]
  simp only [cameraAxis]

/-- The horizontal subspace is the span of the *other* cameras' axes. -/
theorem cameraHorizontalSpace_eq_span (p : ℕ) :
    cameraHorizontalSpace p = Submodule.span ℝ (cameraAxis '' ({p}ᶜ : Set ℕ)) := by
  rw [cameraHorizontalSpace, Finsupp.supported_eq_span_single]
  simp only [cameraAxis]

/-- Atlas completeness: vertical `p` plus horizontal `p` is the whole space. -/
theorem cameraVertical_sup_horizontal (p : ℕ) :
    cameraVerticalLine p ⊔ cameraHorizontalSpace p = ⊤ := by
  rw [cameraVerticalLine, cameraHorizontalSpace, ← Finsupp.supported_union,
    Set.union_compl_self]
  exact Finsupp.supported_univ

/-- Atlas independence: vertical `p` and horizontal `p` are disjoint. -/
theorem cameraVertical_disjoint_horizontal (p : ℕ) :
    Disjoint (cameraVerticalLine p) (cameraHorizontalSpace p) := by
  rw [cameraVerticalLine, cameraHorizontalSpace,
    Finsupp.disjoint_supported_supported_iff]
  exact disjoint_compl_right

/-- The camera atlas is a clean internal direct sum: the horizontal subspace of
`p` is precisely the complement of the vertical line of `p`, i.e. the algebraic
sum of the other cameras' verticals. -/
theorem isCompl_cameraVertical_horizontal (p : ℕ) :
    IsCompl (cameraVerticalLine p) (cameraHorizontalSpace p) :=
  ⟨cameraVertical_disjoint_horizontal p,
    codisjoint_iff.mpr (cameraVertical_sup_horizontal p)⟩

/-- The horizontal part of `n`'s vector (after removing camera `p`'s vertical
voice) lives in the horizontal subspace: what `p` leaves is the other cameras'. -/
theorem factorizationVector_horizontal_mem (n p : ℕ) :
    factorizationVector n - (n.factorization p : ℝ) • cameraAxis p ∈
      cameraHorizontalSpace p := by
  rw [cameraHorizontalSpace, Finsupp.mem_supported]
  have hp0 : (factorizationVector n - (n.factorization p : ℝ) • cameraAxis p) p = 0 := by
    simp [Finsupp.sub_apply, cameraAxis, Finsupp.single_eq_same]
  intro q hq
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  rintro rfl
  rw [Finset.mem_coe, Finsupp.mem_support_iff] at hq
  exact hq hp0

/-- The log functional `e_q ↦ log q` on the camera-log space. -/
noncomputable def logEval : CameraLogSpace →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (fun q : ℕ => Real.log q)

@[simp] theorem logEval_cameraAxis (q : ℕ) : logEval (cameraAxis q) = Real.log q := by
  simp [logEval, cameraAxis]

/-- The log functional recovers `log n` from the quantity's vector: the vector
picture and the scalar log decomposition agree. -/
theorem logEval_factorizationVector {n : ℕ} (hn : n ≠ 0) :
    logEval (factorizationVector n) = Real.log n := by
  have hsupp : (factorizationVector n).support = n.factorization.support := by
    ext q
    rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff, factorizationVector_apply,
      Nat.cast_ne_zero]
  rw [logEval, Finsupp.linearCombination_apply, Finsupp.sum, hsupp,
    log_eq_sum_vertical hn]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [factorizationVector_apply, smul_eq_mul]

/-! ## Detecção no cone positivo e firewall de observabilidade escalar

O ledger escalar detecta o zero no cone aritmético de coordenadas não negativas
suportadas somente em câmeras primas: nele, os pesos logarítmicos positivos não
podem cancelar.  Isto não afirma injetividade entre dois estados positivos
distintos nem constrói ainda um cone de Hilbert.  Fora desse cone, a soma direta
continua exata, mas uma única síntese escalar possui direções cegas.
-/

/-- **Detecção do zero no cone positivo primo.** Se todas as coordenadas são
não negativas e todo eixo material do suporte é primo, `logEval x = 0` força o
estado inteiro a zerar.  Nenhuma injetividade binária no cone é reivindicada. -/
theorem eq_zero_of_logEval_eq_zero_of_nonnegative_prime_support
    {x : CameraLogSpace}
    (hxNonneg : ∀ q, 0 ≤ x q)
    (hxPrime : ∀ q, q ∈ x.support → Nat.Prime q)
    (hlogEval : logEval x = 0) :
    x = 0 := by
  have hsum :
      (∑ q ∈ x.support, x q * Real.log q) = 0 := by
    simpa [logEval, Finsupp.linearCombination_apply, Finsupp.sum,
      smul_eq_mul] using hlogEval
  apply Finsupp.ext
  intro q
  simp only [Finsupp.zero_apply]
  by_contra hq
  have hqmem : q ∈ x.support := Finsupp.mem_support_iff.mpr hq
  have hqPrime := hxPrime q hqmem
  have hxqPos : 0 < x q :=
    lt_of_le_of_ne (hxNonneg q) (Ne.symm hq)
  have hlogqPos : 0 < Real.log q :=
    Real.log_pos (Nat.one_lt_cast.mpr hqPrime.one_lt)
  have htermPos : 0 < x q * Real.log q := mul_pos hxqPos hlogqPos
  have hsingle :
      x q * Real.log q ≤ ∑ r ∈ x.support, x r * Real.log r := by
    apply Finset.single_le_sum
    · intro r hr
      have hrPrime := hxPrime r hr
      exact mul_nonneg (hxNonneg r)
        (Real.log_pos (Nat.one_lt_cast.mpr hrPrime.one_lt)).le
    · exact hqmem
  rw [hsum] at hsingle
  exact (not_lt_of_ge hsingle) htermPos

/-! ## Fora do cone positivo

`IsCompl` prova que as coordenadas do atlas não se perdem dentro do espaço
livre.  Isso não torna uma única síntese escalar injetiva em superposições
reais gerais.  O vetor abaixo registra explicitamente uma direção cega de
`logEval`; ele impede que completude algébrica e fidelidade de um readout sejam
confundidas.
-/

/-- Uma combinação não trivial de dois eixos de câmera cuja síntese logarítmica
se cancela exatamente. -/
noncomputable def logEvalBlindVector : CameraLogSpace :=
  Real.log 3 • cameraAxis 2 - Real.log 2 • cameraAxis 3

@[simp] theorem logEval_logEvalBlindVector :
    logEval logEvalBlindVector = 0 := by
  simp [logEvalBlindVector, mul_comm]

/-- A direção cega explícita é materialmente não nula. -/
theorem logEvalBlindVector_ne_zero : logEvalBlindVector ≠ 0 := by
  intro hzero
  have hcoordinate := congrArg (fun x : CameraLogSpace => x 2) hzero
  have hlog : Real.log (3 : ℝ) = 0 := by
    simpa [logEvalBlindVector, cameraAxis] using hcoordinate
  exact (ne_of_gt (Real.log_pos (by exact Nat.one_lt_ofNat))) hlog

/-- O observador escalar `logEval` não é injetivo no espaço livre completo,
apesar da decomposição interna exata entre cada vertical e seu horizontal. -/
theorem logEval_not_injective : ¬ Function.Injective logEval := by
  intro hinjective
  have hsame : logEval logEvalBlindVector =
      logEval (0 : CameraLogSpace) := by simp
  exact logEvalBlindVector_ne_zero (hinjective hsame)

end CPFormal.Carry.Cp
