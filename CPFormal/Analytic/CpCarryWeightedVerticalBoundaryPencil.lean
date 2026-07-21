import CPFormal.Analytic.CpCarryWeightedVerticalTfvdIdentity
import CPFormal.Analytic.CpGenuineBoundaryPencil

/-!
# Pencil de bordo vertical vestido pela amplitude do carry

Este modulo transforma o traco do TFVD ponderado em um pencil de bordo
literal. Para `0 < q < 1`, os dois tracos sao

`Gamma_0 x = x(0)`,
`Gamma_1 x = q^(-1) x(1) - x(0)`.

O retorno vestido realiza qualquer par de bordo `(a,b)`, enquanto o Green do
bracket reconstrui o interior. Consequentemente, a relacao de bordo livre e o
espaco inteiro `C x C` e todo `lambda` e caracteristico antes de impor uma
restricao aritmetica/Genuine.

Esse resultado e deliberado: o TFVD fornece a geometria livre do bordo, mas
nao seleciona sozinho as ressonancias. O espectro deve nascer da colagem
posterior com a proveniencia nativa, e nao de uma definicao tautologica do
readout.
-/

open scoped BigOperators lp ENNReal NNReal

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Traco de valor: primeira coordenada do traco TFVD vestido. -/
def carryWeightedVerticalBoundaryValueTrace (q : ℝ) :
    CarryVerticalL2 →ₗ[ℂ] ℂ :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ ∘L
    carryWeightedVerticalTrace q).toLinearMap

/-- Traco de fluxo: inclinacao inicial nas unidades de amplitude. -/
def carryWeightedVerticalBoundaryFluxTrace (q : ℝ) :
    CarryVerticalL2 →ₗ[ℂ] ℂ :=
  (ContinuousLinearMap.snd ℂ ℂ ℂ ∘L
    carryWeightedVerticalTrace q).toLinearMap

@[simp] theorem carryWeightedVerticalBoundaryValueTrace_apply
    (q : ℝ) (x : CarryVerticalL2) :
    carryWeightedVerticalBoundaryValueTrace q x = x 0 := by
  simp [carryWeightedVerticalBoundaryValueTrace,
    carryWeightedVerticalTrace_apply]

@[simp] theorem carryWeightedVerticalBoundaryFluxTrace_apply
    (q : ℝ) (x : CarryVerticalL2) :
    carryWeightedVerticalBoundaryFluxTrace q x =
      (q : ℂ)⁻¹ * x 1 - x 0 := by
  simp [carryWeightedVerticalBoundaryFluxTrace,
    carryWeightedVerticalTrace_apply]

/-- Pencil livre da fibra vertical de carry. -/
def carryWeightedVerticalBoundaryPencil (q : ℝ) :
    LinearBoundaryPencil CarryVerticalL2 ℂ where
  valueTrace := carryWeightedVerticalBoundaryValueTrace q
  fluxTrace := carryWeightedVerticalBoundaryFluxTrace q

@[simp] theorem carryWeightedVerticalBoundaryPencil_valueTrace_apply
    (q : ℝ) (x : CarryVerticalL2) :
    (carryWeightedVerticalBoundaryPencil q).valueTrace x = x 0 := by
  rfl

@[simp] theorem carryWeightedVerticalBoundaryPencil_fluxTrace_apply
    (q : ℝ) (x : CarryVerticalL2) :
    (carryWeightedVerticalBoundaryPencil q).fluxTrace x =
      (q : ℂ)⁻¹ * x 1 - x 0 := by
  rfl

/-- Os dois tracos escalares reunidos sao literalmente o traco TFVD. -/
theorem carryWeightedVerticalBoundaryTrace_pair
    (q : ℝ) (x : CarryVerticalL2) :
    ((carryWeightedVerticalBoundaryPencil q).valueTrace x,
      (carryWeightedVerticalBoundaryPencil q).fluxTrace x) =
        carryWeightedVerticalTrace q x := by
  apply Prod.ext <;> simp

/-- Modo de bordo de inclinacao `lambda`, realizado pelo retorno vestido. -/
def carryWeightedVerticalBoundaryMode
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (lambda : ℂ) :
    CarryVerticalL2 :=
  carryWeightedVerticalReturn q hq0 hq1 (1, lambda)

/-- O retorno recupera a coordenada de valor de qualquer dado de bordo. -/
@[simp] theorem carryWeightedVerticalBoundaryValueTrace_return
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (boundary : ℂ × ℂ) :
    carryWeightedVerticalBoundaryValueTrace q
        (carryWeightedVerticalReturn q hqpos.le hq1 boundary) =
      boundary.1 := by
  have htrace :
      carryWeightedVerticalTrace q
          (carryWeightedVerticalReturn q hqpos.le hq1 boundary) =
        boundary := by
    have h := congrArg
      (fun T : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) => T boundary)
      (carryWeightedVerticalTrace_comp_return q hqpos hq1)
    simpa using h
  exact congrArg Prod.fst htrace

/-- O retorno recupera a coordenada de fluxo de qualquer dado de bordo. -/
@[simp] theorem carryWeightedVerticalBoundaryFluxTrace_return
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (boundary : ℂ × ℂ) :
    carryWeightedVerticalBoundaryFluxTrace q
        (carryWeightedVerticalReturn q hqpos.le hq1 boundary) =
      boundary.2 := by
  have htrace :
      carryWeightedVerticalTrace q
          (carryWeightedVerticalReturn q hqpos.le hq1 boundary) =
        boundary := by
    have h := congrArg
      (fun T : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) => T boundary)
      (carryWeightedVerticalTrace_comp_return q hqpos hq1)
    simpa using h
  exact congrArg Prod.snd htrace

@[simp] theorem carryWeightedVerticalBoundaryMode_valueTrace
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) (lambda : ℂ) :
    (carryWeightedVerticalBoundaryPencil q).valueTrace
        (carryWeightedVerticalBoundaryMode q hqpos.le hq1 lambda) = 1 := by
  exact carryWeightedVerticalBoundaryValueTrace_return
    q hqpos hq1 (1, lambda)

@[simp] theorem carryWeightedVerticalBoundaryMode_fluxTrace
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) (lambda : ℂ) :
    (carryWeightedVerticalBoundaryPencil q).fluxTrace
        (carryWeightedVerticalBoundaryMode q hqpos.le hq1 lambda) = lambda := by
  exact carryWeightedVerticalBoundaryFluxTrace_return
    q hqpos hq1 (1, lambda)

/-- O modo de bordo permanece no kernel do bracket interior. -/
@[simp] theorem carryWeightedVerticalBoundaryMode_bracket_eq_zero
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) (lambda : ℂ) :
    carryWeightedVerticalCenteredBracket q
        (carryWeightedVerticalBoundaryMode q hqpos.le hq1 lambda) = 0 := by
  have h := congrArg
    (fun T : (ℂ × ℂ) →L[ℂ] CarryVerticalL2 => T (1, lambda))
    (carryWeightedVerticalCenteredBracket_comp_return q hqpos hq1)
  simpa [carryWeightedVerticalBoundaryMode] using h

/-- A relacao valor--fluxo livre e todo o plano de bordo. -/
theorem carryWeightedVerticalBoundaryRelation_eq_top
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    (carryWeightedVerticalBoundaryPencil q).relation = ⊤ := by
  apply le_antisymm le_top
  intro boundary _
  rcases boundary with ⟨a, b⟩
  change (a, b) ∈ LinearMap.range
    ((carryWeightedVerticalBoundaryPencil q).valueTrace.prod
      (carryWeightedVerticalBoundaryPencil q).fluxTrace)
  refine ⟨carryWeightedVerticalReturn q hqpos.le hq1 (a, b), ?_⟩
  apply Prod.ext
  · simpa [carryWeightedVerticalBoundaryPencil] using
      carryWeightedVerticalBoundaryValueTrace_return
        q hqpos hq1 (a, b)
  · simpa [carryWeightedVerticalBoundaryPencil] using
      carryWeightedVerticalBoundaryFluxTrace_return
        q hqpos hq1 (a, b)

/-- A relacao livre e fechada. -/
theorem carryWeightedVerticalBoundaryRelation_isClosed
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    IsClosed
      ((carryWeightedVerticalBoundaryPencil q).relation : Set (ℂ × ℂ)) := by
  rw [carryWeightedVerticalBoundaryRelation_eq_top q hqpos hq1]
  exact isClosed_univ

/-- Antes da colagem aritmetica, todo `lambda` e caracteristico. -/
theorem carryWeightedVerticalBoundaryPencil_everyValue_isCharacteristic
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) (lambda : ℂ) :
    (carryWeightedVerticalBoundaryPencil q).IsCharacteristicValue lambda := by
  refine ⟨carryWeightedVerticalBoundaryMode q hqpos.le hq1 lambda, ?_, ?_⟩
  · rw [carryWeightedVerticalBoundaryMode_valueTrace q hqpos hq1 lambda]
    norm_num
  · change
      (carryWeightedVerticalBoundaryPencil q).fluxTrace
          (carryWeightedVerticalBoundaryMode q hqpos.le hq1 lambda) -
        lambda •
          (carryWeightedVerticalBoundaryPencil q).valueTrace
            (carryWeightedVerticalBoundaryMode q hqpos.le hq1 lambda) = 0
    rw [carryWeightedVerticalBoundaryMode_fluxTrace q hqpos hq1 lambda,
      carryWeightedVerticalBoundaryMode_valueTrace q hqpos hq1 lambda]
    simp

/-- A identidade TFVD reescrita diretamente pelos dois tracos do pencil. -/
theorem carryWeightedVerticalTfvd_reconstruction_via_boundaryPencil
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (x : CarryVerticalL2) :
    carryVerticalL2WeightedGreen q
          (carryWeightedVerticalCenteredBracket q x) +
        carryWeightedVerticalReturn q hqpos.le hq1
          ((carryWeightedVerticalBoundaryPencil q).valueTrace x,
            (carryWeightedVerticalBoundaryPencil q).fluxTrace x) =
      x := by
  rw [carryWeightedVerticalBoundaryTrace_pair]
  ext n
  exact carryWeightedVerticalTfvd_apply q hqpos hq1 x n

/-- Pencil livre especializado na base material `p`. -/
def primeCarryWeightedVerticalBoundaryPencil (p : ℕ) :
    LinearBoundaryPencil CarryVerticalL2 ℂ :=
  carryWeightedVerticalBoundaryPencil (primeCarryAmplitudeRatio p)

/-- Em toda base material, a relacao livre continua sendo o plano inteiro. -/
theorem primeCarryWeightedVerticalBoundaryRelation_eq_top
    (p : ℕ) (hp : 2 ≤ p) :
    (primeCarryWeightedVerticalBoundaryPencil p).relation = ⊤ := by
  exact carryWeightedVerticalBoundaryRelation_eq_top
    (primeCarryAmplitudeRatio p)
    (primeCarryAmplitudeRatio_pos p (by omega))
    (primeCarryAmplitudeRatio_lt_one p hp)

/-- Nenhuma base material seleciona espectro antes da colagem Genuine. -/
theorem primeCarryWeightedVerticalBoundaryPencil_everyValue_isCharacteristic
    (p : ℕ) (hp : 2 ≤ p) (lambda : ℂ) :
    (primeCarryWeightedVerticalBoundaryPencil p).IsCharacteristicValue lambda := by
  exact carryWeightedVerticalBoundaryPencil_everyValue_isCharacteristic
    (primeCarryAmplitudeRatio p)
    (primeCarryAmplitudeRatio_pos p (by omega))
    (primeCarryAmplitudeRatio_lt_one p hp)
    lambda

end

end CPFormal.Analytic.Cp
