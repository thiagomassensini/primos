import CPFormal.Analytic.CpNativeGpreTfvdGluing

/-!
# Colagem canonica do core nativo de arestas em ell^2

A interface anterior aceitava uma realizacao vertical linear arbitraria. Este
modulo escolhe a realizacao sem parametro e sem normalizacao: um vetor
finitamente suportado de arestas e inserido em `ell^2(N,C)` pela mesma funcao
de coordenadas.

Assim a coordenada `e` usada pelo TFVD e literalmente a coordenada `e` lida
pelo lift `G_pre`. O kernel prova a pertinencia a `ell^2`, a fidelidade da
inclusao, as formulas dos quatro tracos da colagem e a persistencia do
firewall: uma coordenada aritmetica ativa ainda força `lambda` a ser o nivel
material `j`, nao o parametro real de fase.
-/

open scoped lp ENNReal NNReal

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Inclusao canonica de um vetor finitamente suportado no Hilbert vertical. -/
noncomputable def nativeGpreCanonicalVerticalRealization :
    NativeGpreComplexEdgeCore →ₗ[ℂ] CarryVerticalL2 where
  toFun x :=
    ⟨fun n : ℕ => x n, by
      change Memℓp (fun n : ℕ => x n) 2
      rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
      refine summable_of_ne_finset_zero (s := x.support) ?_
      intro n hn
      have hx : x n = 0 := Finsupp.notMem_support_iff.mp hn
      simp [hx]⟩
  map_add' x y := by
    ext n
    rfl
  map_smul' a x := by
    ext n
    rfl

@[simp] theorem nativeGpreCanonicalVerticalRealization_apply
    (x : NativeGpreComplexEdgeCore) (n : ℕ) :
    nativeGpreCanonicalVerticalRealization x n = x n := rfl

/-- A inclusao vertical nao apaga nenhuma coordenada do core. -/
theorem nativeGpreCanonicalVerticalRealization_injective :
    Function.Injective nativeGpreCanonicalVerticalRealization := by
  intro x y hxy
  apply Finsupp.ext
  intro n
  have hcoord := congrArg (fun z : CarryVerticalL2 => z n) hxy
  simpa using hcoord

/-- A colagem diagonal canonica usa o mesmo vetor nas duas pernas. -/
def nativeGpreCanonicalTfvdGlue :
    NativeGpreComplexEdgeCore →ₗ[ℂ] NativeGpreTfvdProductState :=
  nativeGpreTfvdSameEdgeGlue nativeGpreCanonicalVerticalRealization

@[simp] theorem nativeGpreCanonicalTfvdGlue_apply
    (x : NativeGpreComplexEdgeCore) :
    nativeGpreCanonicalTfvdGlue x =
      (nativeGpreCanonicalVerticalRealization x, x) := rfl

/-- A colagem inteira e fiel, independentemente da primeira projecao. -/
theorem nativeGpreCanonicalTfvdGlue_injective :
    Function.Injective nativeGpreCanonicalTfvdGlue := by
  intro x y hxy
  have hsnd := congrArg Prod.snd hxy
  simpa using hsnd

/-- Pencil TFVD--G_pre sem parametro de realizacao. -/
def nativeGpreCanonicalTfvdBoundaryPencil (q : ℝ) :
    LinearBoundaryPencil NativeGpreComplexEdgeCore
      NativeGpreTfvdProductBoundary :=
  nativeGpreTfvdGluedBoundaryPencil q
    nativeGpreCanonicalVerticalRealization

/-- Formula literal do traco de valor canonico. -/
@[simp] theorem nativeGpreCanonicalTfvdBoundaryPencil_valueTrace_apply
    (q : ℝ) (x : NativeGpreComplexEdgeCore) :
    (nativeGpreCanonicalTfvdBoundaryPencil q).valueTrace x =
      (x 0, nativeGpreBoundaryValueLift x) := by
  rfl

/-- Formula literal do traco de fluxo canonico. -/
@[simp] theorem nativeGpreCanonicalTfvdBoundaryPencil_fluxTrace_apply
    (q : ℝ) (x : NativeGpreComplexEdgeCore) :
    (nativeGpreCanonicalTfvdBoundaryPencil q).fluxTrace x =
      ((q : ℂ)⁻¹ * x 1 - x 0,
        nativeGpreBoundaryNumberFluxLift x) := by
  rfl

/-- A relacao canonica permanece contida no produto TFVD--G_pre. -/
theorem nativeGpreCanonicalTfvdBoundaryRelation_le_product
    (q : ℝ) :
    (nativeGpreCanonicalTfvdBoundaryPencil q).relation ≤
      (nativeGpreTfvdProductBoundaryPencil q).relation :=
  nativeGpreTfvdGluedBoundaryRelation_le_product
    q nativeGpreCanonicalVerticalRealization

/-- O TFVD reconstrui exatamente a perna vertical do mesmo vetor nativo. -/
theorem nativeGpreCanonicalTfvd_vertical_reconstruction
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (x : NativeGpreComplexEdgeCore) :
    carryVerticalL2WeightedGreen q
          (carryWeightedVerticalCenteredBracket q
            (nativeGpreCanonicalVerticalRealization x)) +
        carryWeightedVerticalReturn q hqpos.le hq1
          ((nativeGpreCanonicalTfvdBoundaryPencil q).valueTrace x |>.1,
            (nativeGpreCanonicalTfvdBoundaryPencil q).fluxTrace x |>.1) =
      nativeGpreCanonicalVerticalRealization x := by
  change
    carryVerticalL2WeightedGreen q
          (carryWeightedVerticalCenteredBracket q
            (nativeGpreCanonicalVerticalRealization x)) +
        carryWeightedVerticalReturn q hqpos.le hq1
          ((carryWeightedVerticalBoundaryPencil q).valueTrace
              (nativeGpreCanonicalVerticalRealization x),
            (carryWeightedVerticalBoundaryPencil q).fluxTrace
              (nativeGpreCanonicalVerticalRealization x)) =
      nativeGpreCanonicalVerticalRealization x
  exact carryWeightedVerticalTfvd_reconstruction_via_boundaryPencil
    q hqpos hq1 (nativeGpreCanonicalVerticalRealization x)

/-- Mesmo na colagem canonica, uma coordenada de proveniencia ativa impoe o
nivel `j`. -/
theorem nativeGpreCanonicalTfvd_operator_eq_zero_forces_level
    (q : ℝ) (lambda : ℂ) (x : NativeGpreComplexEdgeCore)
    (hzero :
      (nativeGpreCanonicalTfvdBoundaryPencil q).operator lambda x = 0)
    (c : NativeGpreBoundaryContext)
    (hactive : nativeGpreBoundaryValueLift x c ≠ 0) :
    lambda = (c.towerLevel.val : ℂ) := by
  exact nativeGpreTfvdGlued_operator_eq_zero_forces_level
    q nativeGpreCanonicalVerticalRealization lambda x hzero c hactive

/-- Duas alturas materiais ativas distintas impedem o fechamento escalar do
pencil canonico. -/
theorem nativeGpreCanonicalTfvd_no_zero_on_two_distinct_levels
    (q : ℝ) (lambda : ℂ) (x : NativeGpreComplexEdgeCore)
    (c d : NativeGpreBoundaryContext)
    (hc : nativeGpreBoundaryValueLift x c ≠ 0)
    (hd : nativeGpreBoundaryValueLift x d ≠ 0)
    (hlevels : c.towerLevel.val ≠ d.towerLevel.val) :
    (nativeGpreCanonicalTfvdBoundaryPencil q).operator lambda x ≠ 0 := by
  intro hzero
  have hcLevel := nativeGpreCanonicalTfvd_operator_eq_zero_forces_level
    q lambda x hzero c hc
  have hdLevel := nativeGpreCanonicalTfvd_operator_eq_zero_forces_level
    q lambda x hzero d hd
  have hcast : (c.towerLevel.val : ℂ) = (d.towerLevel.val : ℂ) :=
    hcLevel.symm.trans hdLevel
  apply hlevels
  exact_mod_cast hcast

end

end CPFormal.Analytic.Cp
