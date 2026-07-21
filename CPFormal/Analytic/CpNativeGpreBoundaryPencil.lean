import CPFormal.Analytic.CpCarryWeightedVerticalBoundaryPencil
import CPFormal.Analytic.CpNativeGpreTowerLift

/-!
# Pencil de bordo nativo do carrier G_pre

A valvula vertical livre nao seleciona valores caracteristicos. Este modulo
constroi a perna aritmetica que podera restringi-la: o mesmo contexto de
proveniencia e lido duas vezes, uma como valor e outra como fluxo do operador
numero.

O papel `value/numberFlux` deixa de ser uma coordenada esquecivel e passa a
ser a separacao entre `Gamma_0` e `Gamma_1`. Todos os demais eixos permanecem
literais: primo aritmetico, tempo aritmetico, celula, canto, orientacao, perna,
divisor Jordan, primo material e nivel da torre.

O kernel prova que

`Gamma_1 = N Gamma_0`

e que a relacao enriquecida produzida por `G_pre` esta contida no grafo do
operador numero. Ele tambem registra o guardrail espectral local: se o pencil
fecha em `lambda` e uma coordenada de valor no nivel `j` e nao nula, entao
`lambda = j`. Duas coordenadas ativas em niveis distintos impedem o fechamento
do pencil numero puro.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Contexto de bordo com toda a proveniencia, exceto o papel valor--fluxo,
que agora e separado pelos dois tracos do pencil. -/
structure NativeGpreBoundaryContext where
  arithmeticPrime : GpreArithmeticPrime
  time : GpreArithmeticTime
  cell : ℕ
  corner : GpreCorner
  orientation : GpreOrientation
  leg : GpreLeg
  jordanDivisor : GpreJordanDivisor
  towerPrime : GpreTowerPrime
  towerLevel : GpreTowerLevel
  deriving Repr, DecidableEq

namespace NativeGpreBoundaryContext

/-- Recoloca somente o papel de grafo, sem alterar qualquer eixo de
proveniencia. -/
def withRole (c : NativeGpreBoundaryContext)
    (role : GpreGraphRole) : NativeGpreContext where
  arithmeticPrime := c.arithmeticPrime
  time := c.time
  cell := c.cell
  corner := c.corner
  orientation := c.orientation
  role := role
  leg := c.leg
  jordanDivisor := c.jordanDivisor
  towerPrime := c.towerPrime
  towerLevel := c.towerLevel

@[simp] theorem withRole_cell
    (c : NativeGpreBoundaryContext) (role : GpreGraphRole) :
    (c.withRole role).cell = c.cell := rfl

@[simp] theorem withRole_towerLevel
    (c : NativeGpreBoundaryContext) (role : GpreGraphRole) :
    (c.withRole role).towerLevel = c.towerLevel := rfl

end NativeGpreBoundaryContext

/-- Core complexo das arestas, usado pelo pencil espectral. -/
abbrev NativeGpreComplexEdgeCore := ℕ →₀ ℂ

/-- Carrier complexo de bordo com proveniencia integralmente resolvida. -/
abbrev NativeGpreBoundaryCarrier := NativeGpreBoundaryContext → ℂ

/-- Multiplicacao diagonal pelo nivel material da torre. -/
def nativeGpreBoundaryNumberOperator :
    NativeGpreBoundaryCarrier →ₗ[ℂ] NativeGpreBoundaryCarrier where
  toFun y c := (c.towerLevel.val : ℂ) * y c
  map_add' x y := by
    funext c
    simp [mul_add]
  map_smul' a x := by
    funext c
    change (c.towerLevel.val : ℂ) * (a * x c) =
      a * ((c.towerLevel.val : ℂ) * x c)
    ring

@[simp] theorem nativeGpreBoundaryNumberOperator_apply
    (y : NativeGpreBoundaryCarrier) (c : NativeGpreBoundaryContext) :
    nativeGpreBoundaryNumberOperator y c =
      (c.towerLevel.val : ℂ) * y c := rfl

/-- Pencil numero livre no carrier de proveniencia. -/
def nativeGpreTowerNumberBoundaryPencil :
    RegularLinearBoundaryPencil
      NativeGpreBoundaryCarrier NativeGpreBoundaryCarrier where
  valueEquiv := LinearEquiv.refl ℂ NativeGpreBoundaryCarrier
  fluxTrace := nativeGpreBoundaryNumberOperator

@[simp] theorem nativeGpreTowerNumberBoundaryLinearization_apply
    (y : NativeGpreBoundaryCarrier) (c : NativeGpreBoundaryContext) :
    nativeGpreTowerNumberBoundaryPencil.linearization y c =
      (c.towerLevel.val : ℂ) * y c := by
  rfl

/-- Traco de valor complexo do lift nativo. -/
noncomputable def nativeGpreBoundaryValueLift :
    NativeGpreComplexEdgeCore →ₗ[ℂ] NativeGpreBoundaryCarrier where
  toFun x c := x c.cell *
    (nativeGpreTowerCoordinateCoefficient (c.withRole .value) : ℂ)
  map_add' x y := by
    funext c
    simp [add_mul]
  map_smul' a x := by
    funext c
    simp [mul_assoc]

/-- Traco de fluxo numero complexo do mesmo lift nativo. -/
noncomputable def nativeGpreBoundaryNumberFluxLift :
    NativeGpreComplexEdgeCore →ₗ[ℂ] NativeGpreBoundaryCarrier where
  toFun x c := x c.cell *
    (nativeGpreTowerCoordinateCoefficient (c.withRole .numberFlux) : ℂ)
  map_add' x y := by
    funext c
    simp [add_mul]
  map_smul' a x := by
    funext c
    simp [mul_assoc]

@[simp] theorem nativeGpreBoundaryValueLift_apply
    (x : NativeGpreComplexEdgeCore) (c : NativeGpreBoundaryContext) :
    nativeGpreBoundaryValueLift x c = x c.cell *
      (nativeGpreTowerCoordinateCoefficient (c.withRole .value) : ℂ) := rfl

@[simp] theorem nativeGpreBoundaryNumberFluxLift_apply
    (x : NativeGpreComplexEdgeCore) (c : NativeGpreBoundaryContext) :
    nativeGpreBoundaryNumberFluxLift x c = x c.cell *
      (nativeGpreTowerCoordinateCoefficient (c.withRole .numberFlux) : ℂ) := rfl

/-- O coeficiente de fluxo e exatamente `j` vezes o coeficiente de valor. -/
theorem nativeGpreBoundary_numberFluxCoefficient_eq_level_mul_value
    (c : NativeGpreBoundaryContext) :
    nativeGpreTowerCoordinateCoefficient (c.withRole .numberFlux) =
      (c.towerLevel.val : ℝ) *
        nativeGpreTowerCoordinateCoefficient (c.withRole .value) := by
  by_cases hcell : c.cell = 0
  · simp [nativeGpreTowerCoordinateCoefficient,
      NativeGpreBoundaryContext.withRole, hcell]
  by_cases htower : c.towerPrime.val = c.arithmeticPrime.val
  · let u := nativeGpreCornerU c.cell c.corner
    let v := nativeGpreCornerV c.cell c.corner
    by_cases hd : c.jordanDivisor.val ∣ Nat.gcd u v
    · simp [nativeGpreTowerCoordinateCoefficient,
        NativeGpreBoundaryContext.withRole, hcell, htower, hd,
        u, v, nativeGpreGraphRoleFactor]
      ring
    · simp [nativeGpreTowerCoordinateCoefficient,
        NativeGpreBoundaryContext.withRole, hcell, htower, hd,
        u, v]
  · simp [nativeGpreTowerCoordinateCoefficient,
      NativeGpreBoundaryContext.withRole, hcell, htower]

/-- Forma complexa da lei `Gamma_1 = N Gamma_0`, coordenada por coordenada. -/
theorem nativeGpreBoundaryNumberFluxLift_apply_eq_level_mul_value
    (x : NativeGpreComplexEdgeCore) (c : NativeGpreBoundaryContext) :
    nativeGpreBoundaryNumberFluxLift x c =
      (c.towerLevel.val : ℂ) * nativeGpreBoundaryValueLift x c := by
  rw [nativeGpreBoundaryNumberFluxLift_apply,
    nativeGpreBoundaryValueLift_apply,
    nativeGpreBoundary_numberFluxCoefficient_eq_level_mul_value]
  push_cast
  ring

/-- Igualdade de mapas: o fluxo nativo e o operador numero aplicado ao valor. -/
theorem nativeGpreBoundaryNumberFluxLift_eq_numberOperator_comp_valueLift :
    nativeGpreBoundaryNumberFluxLift =
      nativeGpreBoundaryNumberOperator.comp nativeGpreBoundaryValueLift := by
  ext x c
  exact nativeGpreBoundaryNumberFluxLift_apply_eq_level_mul_value x c

/-- Pencil de proveniencia produzido pelo lift concreto de `G_pre`. -/
def nativeGpreProvenanceBoundaryPencil :
    LinearBoundaryPencil NativeGpreComplexEdgeCore NativeGpreBoundaryCarrier where
  valueTrace := nativeGpreBoundaryValueLift
  fluxTrace := nativeGpreBoundaryNumberFluxLift

/-- A relacao de proveniencia de `G_pre` esta contida no grafo numero livre. -/
theorem nativeGpreProvenanceBoundaryRelation_le_numberGraph :
    nativeGpreProvenanceBoundaryPencil.relation ≤
      nativeGpreTowerNumberBoundaryPencil.toLinearBoundaryPencil.relation := by
  intro z hz
  change z ∈ LinearMap.range
    (nativeGpreBoundaryValueLift.prod nativeGpreBoundaryNumberFluxLift) at hz
  rcases hz with ⟨x, rfl⟩
  change
    (nativeGpreBoundaryValueLift x, nativeGpreBoundaryNumberFluxLift x) ∈
      LinearMap.range
        (nativeGpreTowerNumberBoundaryPencil.toLinearBoundaryPencil.valueTrace.prod
          nativeGpreTowerNumberBoundaryPencil.toLinearBoundaryPencil.fluxTrace)
  refine ⟨nativeGpreBoundaryValueLift x, ?_⟩
  apply Prod.ext
  · rfl
  · change nativeGpreBoundaryNumberOperator (nativeGpreBoundaryValueLift x) =
      nativeGpreBoundaryNumberFluxLift x
    rw [nativeGpreBoundaryNumberFluxLift_eq_numberOperator_comp_valueLift]
    rfl

/-- Formula local do operador do pencil enriquecido. -/
@[simp] theorem nativeGpreProvenanceBoundaryPencil_operator_apply
    (lambda : ℂ) (x : NativeGpreComplexEdgeCore)
    (c : NativeGpreBoundaryContext) :
    nativeGpreProvenanceBoundaryPencil.operator lambda x c =
      ((c.towerLevel.val : ℂ) - lambda) *
        nativeGpreBoundaryValueLift x c := by
  change nativeGpreBoundaryNumberFluxLift x c -
      lambda * nativeGpreBoundaryValueLift x c = _
  rw [nativeGpreBoundaryNumberFluxLift_apply_eq_level_mul_value]
  ring

/-- Se o pencil fecha e uma coordenada de valor e ativa, o valor
caracteristico coincide com o nivel material dessa coordenada. -/
theorem nativeGpreProvenanceBoundaryPencil_operator_eq_zero_forces_level
    (lambda : ℂ) (x : NativeGpreComplexEdgeCore)
    (hzero : nativeGpreProvenanceBoundaryPencil.operator lambda x = 0)
    (c : NativeGpreBoundaryContext)
    (hactive : nativeGpreBoundaryValueLift x c ≠ 0) :
    lambda = (c.towerLevel.val : ℂ) := by
  have hcoord := congrFun hzero c
  have hmul :
      ((c.towerLevel.val : ℂ) - lambda) *
          nativeGpreBoundaryValueLift x c = 0 := by
    simpa using hcoord
  have hfactor : (c.towerLevel.val : ℂ) - lambda = 0 :=
    (mul_eq_zero.mp hmul).resolve_right hactive
  exact (sub_eq_zero.mp hfactor).symm

/-- Duas coordenadas ativas em niveis distintos impedem o fechamento do
pencil numero puro. -/
theorem nativeGpreProvenanceBoundaryPencil_no_zero_on_two_distinct_levels
    (lambda : ℂ) (x : NativeGpreComplexEdgeCore)
    (c d : NativeGpreBoundaryContext)
    (hc : nativeGpreBoundaryValueLift x c ≠ 0)
    (hd : nativeGpreBoundaryValueLift x d ≠ 0)
    (hlevels : c.towerLevel.val ≠ d.towerLevel.val) :
    nativeGpreProvenanceBoundaryPencil.operator lambda x ≠ 0 := by
  intro hzero
  have hcLevel :=
    nativeGpreProvenanceBoundaryPencil_operator_eq_zero_forces_level
      lambda x hzero c hc
  have hdLevel :=
    nativeGpreProvenanceBoundaryPencil_operator_eq_zero_forces_level
      lambda x hzero d hd
  have hcast : (c.towerLevel.val : ℂ) = (d.towerLevel.val : ℂ) :=
    hcLevel.symm.trans hdLevel
  apply hlevels
  exact_mod_cast hcast

end

end CPFormal.Analytic.Cp
