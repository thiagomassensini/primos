import CPFormal.Analytic.CpInfiniteRealSpectralGenerator
import Mathlib.LinearAlgebra.Prod
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Pencil de bordo Genuine e linearizacao de valores caracteristicos

Este modulo fixa a interface operatorial do bordo:

* um pencil linear e um par valor--fluxo;
* sua relacao de bordo e o range do mapa conjunto;
* `lambda` e caracteristico exatamente quando a relacao contem uma direcao
  de inclinacao `lambda`;
* quando o traco de valor e uma equivalencia, o pencil lineariza num
  endomorfismo ordinario.

A compressao escalar Genuine fornece um primeiro pencil fechado e prova que
uma ressonancia real e exatamente o valor caracteristico zero. Ela nao
substitui a relacao enriquecida nativa: a colagem dos canais C2/Cp, com
proveniencia e nivel primo-potencia preservados, permanece um gate separado.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Pencil linear de bordo, escrito como traco de valor e traco de fluxo. -/
structure LinearBoundaryPencil (X B : Type*)
    [AddCommGroup X] [Module ℂ X]
    [AddCommGroup B] [Module ℂ B] where
  valueTrace : X →ₗ[ℂ] B
  fluxTrace : X →ₗ[ℂ] B

namespace LinearBoundaryPencil

variable {X B : Type*}
  [AddCommGroup X] [Module ℂ X]
  [AddCommGroup B] [Module ℂ B]

/-- Operador do pencil `Gamma_1 - lambda Gamma_0`. -/
def operator (P : LinearBoundaryPencil X B) (lambda : ℂ) : X →ₗ[ℂ] B :=
  P.fluxTrace - lambda • P.valueTrace

@[simp] theorem operator_apply (P : LinearBoundaryPencil X B)
    (lambda : ℂ) (x : X) :
    P.operator lambda x = P.fluxTrace x - lambda • P.valueTrace x := rfl

/-- Relacao valor--fluxo do bordo. -/
def relation (P : LinearBoundaryPencil X B) : Submodule ℂ (B × B) :=
  LinearMap.range (P.valueTrace.prod P.fluxTrace)

/-- `lambda` e caracteristico quando o pencil fecha num estado com valor de
bordo nao nulo. -/
def IsCharacteristicValue (P : LinearBoundaryPencil X B) (lambda : ℂ) : Prop :=
  ∃ x : X, P.valueTrace x ≠ 0 ∧ P.operator lambda x = 0

/-- A mesma condicao vista diretamente como inclinacao da relacao. -/
def RelationHasSlope (P : LinearBoundaryPencil X B) (lambda : ℂ) : Prop :=
  ∃ u : B, u ≠ 0 ∧ (u, lambda • u) ∈ P.relation

/-- Valores caracteristicos sao exatamente as inclinacoes nao triviais da
relacao de bordo. -/
theorem isCharacteristicValue_iff_relationHasSlope
    (P : LinearBoundaryPencil X B) (lambda : ℂ) :
    P.IsCharacteristicValue lambda ↔ P.RelationHasSlope lambda := by
  constructor
  · rintro ⟨x, hx, hzero⟩
    change P.fluxTrace x - lambda • P.valueTrace x = 0 at hzero
    refine ⟨P.valueTrace x, hx, ?_⟩
    change (P.valueTrace x, lambda • P.valueTrace x) ∈
      LinearMap.range (P.valueTrace.prod P.fluxTrace)
    refine ⟨x, ?_⟩
    change (P.valueTrace x, P.fluxTrace x) =
      (P.valueTrace x, lambda • P.valueTrace x)
    apply Prod.ext
    · rfl
    · exact sub_eq_zero.mp hzero
  · rintro ⟨u, hu, hrelation⟩
    change (u, lambda • u) ∈
      LinearMap.range (P.valueTrace.prod P.fluxTrace) at hrelation
    rcases hrelation with ⟨x, hx⟩
    have hvalue := congrArg Prod.fst hx
    have hflux := congrArg Prod.snd hx
    change P.valueTrace x = u at hvalue
    change P.fluxTrace x = lambda • u at hflux
    refine ⟨x, ?_, ?_⟩
    · intro hzero
      apply hu
      rw [← hvalue, hzero]
    · change P.fluxTrace x - lambda • P.valueTrace x = 0
      rw [hvalue, hflux]
      simp

end LinearBoundaryPencil

/-- Pencil regular: o traco de valor identifica estados e valores de bordo. -/
structure RegularLinearBoundaryPencil (X B : Type*)
    [AddCommGroup X] [Module ℂ X]
    [AddCommGroup B] [Module ℂ B] where
  valueEquiv : X ≃ₗ[ℂ] B
  fluxTrace : X →ₗ[ℂ] B

namespace RegularLinearBoundaryPencil

variable {X B : Type*}
  [AddCommGroup X] [Module ℂ X]
  [AddCommGroup B] [Module ℂ B]

/-- Esquece a regularidade, mantendo o pencil valor--fluxo. -/
def toLinearBoundaryPencil (P : RegularLinearBoundaryPencil X B) :
    LinearBoundaryPencil X B where
  valueTrace := P.valueEquiv.toLinearMap
  fluxTrace := P.fluxTrace

/-- Linearizacao ordinaria `Gamma_0^{-1} Gamma_1`. -/
def linearization (P : RegularLinearBoundaryPencil X B) : X →ₗ[ℂ] X :=
  P.valueEquiv.symm.toLinearMap.comp P.fluxTrace

@[simp] theorem linearization_apply
    (P : RegularLinearBoundaryPencil X B) (x : X) :
    P.linearization x = P.valueEquiv.symm (P.fluxTrace x) := rfl

/-- A equacao do pencil e exatamente a equacao de autovetor da linearizacao. -/
theorem linearization_eq_smul_iff
    (P : RegularLinearBoundaryPencil X B) (lambda : ℂ) (x : X) :
    P.linearization x = lambda • x ↔
      P.fluxTrace x = lambda • P.valueEquiv x := by
  constructor
  · intro h
    have h' := congrArg P.valueEquiv h
    simpa [linearization] using h'
  · intro h
    apply P.valueEquiv.injective
    simpa [linearization] using h

/-- Valores caracteristicos de um pencil regular sao autovalores da
linearizacao, com autovetor nao nulo. -/
theorem isCharacteristicValue_iff_eigenpair
    (P : RegularLinearBoundaryPencil X B) (lambda : ℂ) :
    P.toLinearBoundaryPencil.IsCharacteristicValue lambda ↔
      ∃ x : X, x ≠ 0 ∧ P.linearization x = lambda • x := by
  constructor
  · rintro ⟨x, hvalue, hoperator⟩
    change P.valueEquiv x ≠ 0 at hvalue
    change P.fluxTrace x - lambda • P.valueEquiv x = 0 at hoperator
    refine ⟨x, ?_, ?_⟩
    · intro hx
      apply hvalue
      subst x
      simp
    · apply (P.linearization_eq_smul_iff lambda x).2
      exact sub_eq_zero.mp hoperator
  · rintro ⟨x, hx, heigen⟩
    refine ⟨x, ?_, ?_⟩
    · change P.valueEquiv x ≠ 0
      intro hvalue
      apply hx
      exact P.valueEquiv.injective (by simpa using hvalue)
    · change P.fluxTrace x - lambda • P.valueEquiv x = 0
      exact sub_eq_zero.mpr
        ((P.linearization_eq_smul_iff lambda x).1 heigen)

end RegularLinearBoundaryPencil

/-- Fluxo escalar Genuine na altura real `t`. -/
def realSpectralGenuineBoundaryFlux (t : ℝ) : ℂ →ₗ[ℂ] ℂ where
  toFun z := realSpectralGenuine t * z
  map_add' x y := by ring
  map_smul' c x := by simp [mul_assoc, mul_left_comm]

@[simp] theorem realSpectralGenuineBoundaryFlux_apply (t : ℝ) (z : ℂ) :
    realSpectralGenuineBoundaryFlux t z = realSpectralGenuine t * z := rfl

/-- Pencil escalar comprimido do readout Genuine. -/
def realSpectralGenuineBoundaryPencil (t : ℝ) :
    RegularLinearBoundaryPencil ℂ ℂ where
  valueEquiv := LinearEquiv.refl ℂ ℂ
  fluxTrace := realSpectralGenuineBoundaryFlux t

@[simp] theorem realSpectralGenuineBoundaryLinearization_apply
    (t : ℝ) (z : ℂ) :
    (realSpectralGenuineBoundaryPencil t).linearization z =
      realSpectralGenuine t * z := by
  rfl

/-- O unico valor caracteristico do pencil escalar e o proprio readout
Genuine. -/
theorem realSpectralGenuine_isCharacteristicValue_iff
    (t : ℝ) (lambda : ℂ) :
    (realSpectralGenuineBoundaryPencil t).toLinearBoundaryPencil.IsCharacteristicValue lambda ↔
      lambda = realSpectralGenuine t := by
  constructor
  · rintro ⟨z, hz, hzero⟩
    change z ≠ 0 at hz
    change realSpectralGenuine t * z - lambda * z = 0 at hzero
    have hmul : (realSpectralGenuine t - lambda) * z = 0 := by
      rw [sub_mul]
      exact hzero
    have hcoeff : realSpectralGenuine t - lambda = 0 :=
      (mul_eq_zero.mp hmul).resolve_right hz
    exact (sub_eq_zero.mp hcoeff).symm
  · intro hlambda
    subst lambda
    refine ⟨1, ?_, ?_⟩
    · change (1 : ℂ) ≠ 0
      norm_num
    · change realSpectralGenuine t * 1 - realSpectralGenuine t * 1 = 0
      ring

/-- Ressonancia Genuine equivale ao valor caracteristico zero. -/
theorem isRealSpectralResonance_iff_zero_characteristicValue (t : ℝ) :
    IsRealSpectralResonance t ↔
      (realSpectralGenuineBoundaryPencil t).toLinearBoundaryPencil.IsCharacteristicValue 0 := by
  simpa [IsRealSpectralResonance, eq_comm] using
    (realSpectralGenuine_isCharacteristicValue_iff t 0).symm

/-- Forma linearizada: ressonancia equivale a um kernel nao trivial. -/
theorem isRealSpectralResonance_iff_linearized_kernel (t : ℝ) :
    IsRealSpectralResonance t ↔
      ∃ z : ℂ, z ≠ 0 ∧
        (realSpectralGenuineBoundaryPencil t).linearization z = 0 := by
  rw [isRealSpectralResonance_iff_zero_characteristicValue]
  simpa using
    (RegularLinearBoundaryPencil.isCharacteristicValue_iff_eigenpair
      (realSpectralGenuineBoundaryPencil t) 0)

/-- A relacao escalar e fechada; isto e automatico em dimensao finita. -/
theorem realSpectralGenuineBoundaryRelation_isClosed (t : ℝ) :
    IsClosed
      ((realSpectralGenuineBoundaryPencil t).toLinearBoundaryPencil.relation :
        Set (ℂ × ℂ)) :=
  ((realSpectralGenuineBoundaryPencil t).toLinearBoundaryPencil.relation).closed_of_finiteDimensional

end

end CPFormal.Analytic.Cp
