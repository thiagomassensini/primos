import CPFormal.Analytic.CpFiniteSeededTfvdGreenIdentity
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Group.HomCompletion

/-!
# Continuidade do lift de proveniencia e no-go do grafo numero

Este modulo formaliza a metade topologica do preflight da 0.50 sem declarar
o fechamento radial. Os indices que pertencem a eixos diferentes recebem
tipos diferentes; em particular, o divisor de Jordan, o tempo aritmetico e o
nivel da torre nao podem ser identificados por reducao definicional.

O ledger exato da majorante e

`(25 * 4/3 * 4/3 * 1/3 + 4) * 9 * 4 * 2 * 2 * 2 * 2 = 32512/3 < 128^2`.

Um certificado do lift nativo deve fornecer somente a estimativa quadrada
com a primeira constante. O kernel deduz a cota de norma `128`, empacota o
mapa continuo e o estende de modo canonico a completacao do dominio.

A segunda parte e um no-go incondicional. O grafo de qualquer isometria e
neutro para sua forma canonica de valor--fluxo, enquanto a primeira celula
Green possui o witness exato `G(delta_4, delta_2)=1/2`. Logo o grafo numero de
Qtilde nao pode, sozinho, representar a forma Green/Stokes. Uma lei final
precisa conter um acoplamento TFVD--Qtilde independente do alvo radial.
-/

open scoped BigOperators

namespace CPFormal.Analytic.Cp

noncomputable section

/-!
## Carrier tipado da proveniencia
-/

/-- Primo da camera aritmetica. -/
structure GpreArithmeticPrime where
  val : ℕ
  deriving Repr, DecidableEq

/-- Tempo inteiro do ledger aritmetico. Nao e a altura espectral. -/
structure GpreArithmeticTime where
  val : ℕ
  deriving Repr, DecidableEq

/-- Divisor resolvido do canal de Jordan. -/
structure GpreJordanDivisor where
  val : ℕ
  deriving Repr, DecidableEq

/-- Primo material da torre enriquecida. -/
structure GpreTowerPrime where
  val : ℕ
  deriving Repr, DecidableEq

/-- Nivel material da torre. Nao e o divisor de Jordan. -/
structure GpreTowerLevel where
  val : ℕ
  deriving Repr, DecidableEq

/-- Os quatro cantos nativos de uma celula C2. -/
inductive GpreCorner where
  | lowerLeft
  | lowerRight
  | upperLeft
  | upperRight
  deriving Repr, DecidableEq

/-- Orientacao original ou completacao reciproca. -/
inductive GpreOrientation where
  | original
  | reciprocal
  deriving Repr, DecidableEq

/-- As duas pernas preservadas antes da forma de bordo. -/
inductive GpreLeg where
  | left
  | right
  deriving Repr, DecidableEq

/-- Papel do canal no par valor--fluxo do grafo. -/
inductive GpreGraphRole where
  | value
  | numberFlux
  deriving Repr, DecidableEq

/-- Contexto discreto completo. Campos semanticamente distintos continuam
distintos no tipo, mesmo quando seus valores subjacentes sao naturais. -/
structure NativeGpreContext where
  arithmeticPrime : GpreArithmeticPrime
  time : GpreArithmeticTime
  cell : ℕ
  corner : GpreCorner
  orientation : GpreOrientation
  role : GpreGraphRole
  leg : GpreLeg
  jordanDivisor : GpreJordanDivisor
  towerPrime : GpreTowerPrime
  towerLevel : GpreTowerLevel
  deriving Repr, DecidableEq

/-- Peso de contagem fixo, anterior ao cutoff e ao parametro espectral. -/
def nativeGpreCountingWeight (_ : NativeGpreContext) : ℝ := 1

@[simp] theorem nativeGpreCountingWeight_eq_one (c : NativeGpreContext) :
    nativeGpreCountingWeight c = 1 := rfl

theorem nativeGpreCountingWeight_pos (c : NativeGpreContext) :
    0 < nativeGpreCountingWeight c := by
  simp

/-- Perfil de torre nativo `p^(-j*tau)/j`, com o nivel zero separado. -/
def nativeUnitMassTowerProfile (p tau j : ℕ) : ℝ :=
  if j = 0 then 0 else (((p : ℝ) ^ (j * tau))⁻¹) / (j : ℝ)

@[simp] theorem nativeUnitMassTowerProfile_zero_level (p tau : ℕ) :
    nativeUnitMassTowerProfile p tau 0 = 0 := by
  simp [nativeUnitMassTowerProfile]

@[simp] theorem nativeUnitMassTowerProfile_zero_time
    (p j : ℕ) (hj : j ≠ 0) :
    nativeUnitMassTowerProfile p 0 j = (j : ℝ)⁻¹ := by
  simp [nativeUnitMassTowerProfile, hj, div_eq_mul_inv]

/-!
## Ledger exato da constante 128
-/

/-- Majorante por canto: tempos positivos `400/27` mais endpoint `4`. -/
def nativeGprePerCornerSquareBound : ℚ :=
  25 * (4 / 3) * (4 / 3) * (1 / 3) + 4

/-- Majorante quadrada global, incluindo todas as multiplicidades tipadas. -/
def nativeGpreGraphSquareLedger : ℚ :=
  nativeGprePerCornerSquareBound * 9 * 4 * 2 * 2 * 2 * 2

/-- A constante do ledger como numero real, usada nas estimativas de norma. -/
def nativeGpreGraphSquareBound : ℝ :=
  (nativeGpreGraphSquareLedger : ℝ)

theorem nativeGprePerCornerSquareBound_eq :
    nativeGprePerCornerSquareBound = 508 / 27 := by
  norm_num [nativeGprePerCornerSquareBound]

theorem nativeGpreGraphSquareLedger_eq :
    nativeGpreGraphSquareLedger = 32512 / 3 := by
  norm_num [nativeGpreGraphSquareLedger, nativeGprePerCornerSquareBound]

theorem nativeGpreGraphSquareBound_eq :
    nativeGpreGraphSquareBound = (32512 : ℝ) / 3 := by
  norm_num [nativeGpreGraphSquareBound, nativeGpreGraphSquareLedger,
    nativeGprePerCornerSquareBound]

theorem nativeGpreGraphSquareBound_lt_128_sq :
    nativeGpreGraphSquareBound < (128 : ℝ) ^ 2 := by
  rw [nativeGpreGraphSquareBound_eq]
  norm_num

/-!
## Do majorante quadrado ao lift continuo
-/

variable {𝕜 X Y : Type*}
variable [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- Certificado tipado da metade aritmetica. Construir um valor desta
estrutura para o `G_pre` nativo exige provar a majorante local do preflight;
nenhuma lei Green ou hipotese de zero aparece no campo. -/
structure NativeGpreTowerLiftCertificate where
  toLinearMap : X →ₗ[𝕜] Y
  graphNormSq_le : ∀ x : X,
    ‖toLinearMap x‖ ^ 2 ≤ nativeGpreGraphSquareBound * ‖x‖ ^ 2

/-- A conta exata do ledger transforma a majorante quadrada na cota `128`. -/
theorem NativeGpreTowerLiftCertificate.graphNorm_le
    (certificate : NativeGpreTowerLiftCertificate (𝕜 := 𝕜) (X := X) (Y := Y))
    (x : X) :
    ‖certificate.toLinearMap x‖ ≤ (128 : ℝ) * ‖x‖ := by
  have hsquare := certificate.graphNormSq_le x
  have hconstant :
      nativeGpreGraphSquareBound ≤ (128 : ℝ) ^ 2 :=
    le_of_lt nativeGpreGraphSquareBound_lt_128_sq
  have hscale :
      nativeGpreGraphSquareBound * ‖x‖ ^ 2 ≤
        (128 : ℝ) ^ 2 * ‖x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hconstant (sq_nonneg ‖x‖)
  have htotal :
      ‖certificate.toLinearMap x‖ ^ 2 ≤
        (128 : ℝ) ^ 2 * ‖x‖ ^ 2 :=
    hsquare.trans hscale
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  have hy : 0 ≤ ‖certificate.toLinearMap x‖ :=
    norm_nonneg (certificate.toLinearMap x)
  nlinarith

/-- O lift certificado como aplicacao linear continua. -/
def NativeGpreTowerLiftCertificate.toContinuousLinearMap
    (certificate : NativeGpreTowerLiftCertificate (𝕜 := 𝕜) (X := X) (Y := Y)) :
    X →L[𝕜] Y :=
  certificate.toLinearMap.mkContinuous 128 certificate.graphNorm_le

theorem NativeGpreTowerLiftCertificate.norm_toContinuousLinearMap_le
    (certificate : NativeGpreTowerLiftCertificate (𝕜 := 𝕜) (X := X) (Y := Y)) :
    ‖certificate.toContinuousLinearMap‖ ≤ 128 := by
  exact LinearMap.mkContinuous_norm_le _ (by norm_num) certificate.graphNorm_le

/-- A mesma aplicacao como homomorfismo aditivo normado. Esta e a interface
consumida pela propriedade universal da completacao. -/
def NativeGpreTowerLiftCertificate.toNormedAddGroupHom
    (certificate : NativeGpreTowerLiftCertificate (𝕜 := 𝕜) (X := X) (Y := Y)) :
    NormedAddGroupHom X Y :=
  certificate.toLinearMap.toAddMonoidHom.mkNormedAddGroupHom
    128 certificate.graphNorm_le

theorem NativeGpreTowerLiftCertificate.norm_toNormedAddGroupHom_le
    (certificate : NativeGpreTowerLiftCertificate (𝕜 := 𝕜) (X := X) (Y := Y)) :
    ‖certificate.toNormedAddGroupHom‖ ≤ 128 := by
  exact AddMonoidHom.mkNormedAddGroupHom_norm_le _ (by norm_num)
    certificate.graphNorm_le

variable [T0Space Y] [CompleteSpace Y]

/-- Extensao continua canonica do lift a completacao Green/Hardy do core. -/
def NativeGpreTowerLiftCertificate.completionExtension
    (certificate : NativeGpreTowerLiftCertificate (𝕜 := 𝕜) (X := X) (Y := Y)) :
    NormedAddGroupHom (UniformSpace.Completion X) Y :=
  certificate.toNormedAddGroupHom.extension

@[simp] theorem NativeGpreTowerLiftCertificate.completionExtension_coe
    (certificate : NativeGpreTowerLiftCertificate (𝕜 := 𝕜) (X := X) (Y := Y))
    (x : X) :
    certificate.completionExtension (x : UniformSpace.Completion X) =
      certificate.toLinearMap x := by
  exact NormedAddGroupHom.extension_coe certificate.toNormedAddGroupHom x

/-!
## Neutralidade do grafo numero
-/

variable {𝕜₀ H0 Hminus : Type*}
variable [RCLike 𝕜₀]
variable [NormedAddCommGroup H0] [InnerProductSpace 𝕜₀ H0]
variable [NormedAddCommGroup Hminus] [InnerProductSpace 𝕜₀ Hminus]

/-- Forma canonica valor--fluxo induzida pelo grafo de uma isometria. -/
def qtildeNumberGraphBoundaryForm
    (numberOperator : H0 →ₗᵢ[𝕜₀] Hminus) (x y : H0) : 𝕜₀ :=
  ⟪numberOperator x, numberOperator y⟫_𝕜₀ - ⟪x, y⟫_𝕜₀

/-- O grafo numero e neutro em todos os pares, nao apenas na curva Genuine. -/
@[simp] theorem qtildeNumberGraphBoundaryForm_eq_zero
    (numberOperator : H0 →ₗᵢ[𝕜₀] Hminus) (x y : H0) :
    qtildeNumberGraphBoundaryForm numberOperator x y = 0 := by
  rw [qtildeNumberGraphBoundaryForm, numberOperator.inner_map_map]
  exact sub_self _

/-!
## Witness Green finito e no-go
-/

/-- Core finito de vertices usado pelo witness da primeira celula. -/
abbrev NativeGreenVertexCore := ℕ →₀ ℝ

/-- Kernel Green reduzido da primeira aresta, com todos os seis coeficientes
na orientacao assinada do preflight. -/
def firstCellReducedGreenKernel : ℕ → ℕ → ℝ
  | 1, 2 => -(1 / 2)
  | 1, 4 => 1 / 4
  | 2, 1 => 1
  | 2, 4 => -(1 / 4)
  | 4, 1 => -1
  | 4, 2 => 1 / 2
  | _, _ => 0

/-- Forma bilinear finita associada ao kernel da primeira celula. -/
def firstCellReducedGreenForm
    (x y : NativeGreenVertexCore) : ℝ :=
  x.sum fun u xu ↦
    y.sum fun v yv ↦ xu * firstCellReducedGreenKernel u v * yv

/-- Vetor delta no vertice `n`. -/
def nativeGreenDelta (n : ℕ) : NativeGreenVertexCore :=
  Finsupp.single n 1

/-- Witness exato: a forma Green ja e nao nula na primeira celula. -/
theorem firstCellReducedGreenForm_delta_four_delta_two :
    firstCellReducedGreenForm (nativeGreenDelta 4) (nativeGreenDelta 2) =
      (1 : ℝ) / 2 := by
  simp [firstCellReducedGreenForm, nativeGreenDelta,
    firstCellReducedGreenKernel]

/-- Nenhum pullback do grafo de uma isometria por um lift linear pode
coincidir com a forma Green inteira no core: o lado do grafo zera
identicamente, mas o witness Green vale `1/2`. -/
theorem qtildeNumberGraph_cannot_represent_firstCellGreen
    {H0R HminusR : Type*}
    [NormedAddCommGroup H0R] [InnerProductSpace ℝ H0R]
    [NormedAddCommGroup HminusR] [InnerProductSpace ℝ HminusR]
    (numberOperator : H0R →ₗᵢ[ℝ] HminusR)
    (arithmeticLift : NativeGreenVertexCore →ₗ[ℝ] H0R) :
    ¬ ∀ x y : NativeGreenVertexCore,
      qtildeNumberGraphBoundaryForm numberOperator
          (arithmeticLift x) (arithmeticLift y) =
        firstCellReducedGreenForm x y := by
  intro hrepresentation
  have hwitness :=
    hrepresentation (nativeGreenDelta 4) (nativeGreenDelta 2)
  rw [qtildeNumberGraphBoundaryForm_eq_zero,
    firstCellReducedGreenForm_delta_four_delta_two] at hwitness
  norm_num at hwitness

end

end CPFormal.Analytic.Cp
