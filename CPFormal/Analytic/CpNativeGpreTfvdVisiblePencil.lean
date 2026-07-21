import CPFormal.Analytic.CpNativeGpreTfvdAnalysis

/-!
# Compressao visivel do range TFVD--G_pre

A analise enriquecida preserva bracket, traco e as duas pernas de proveniencia.
Este modulo acrescenta somente um observador escalar continuo do estado
reconstruido. Assim a visibilidade e uma compressao do carrier nativo fechado,
nao uma anulacao coordenada da proveniencia.

Para um estado `x`, restringimos o carrier a orbita unidimensional `z |-> z x`.
O pencil resultante possui coeficiente caracteristico igual ao readout visivel
`observer x`. Logo zero e caracteristico exatamente quando o observador fecha,
enquanto o estado enriquecido pode permanecer nao nulo.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Observador visivel no carrier enriquecido: primeiro reconstrui o estado
vertical pelo TFVD e somente depois aplica um funcional escalar escolhido. -/
def nativeGpreFiniteTfvdVisibleReadout
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (observer : CarryVerticalL2 →L[ℂ] ℂ) :
    NativeGpreFiniteTfvdAnalysisCarrier S →L[ℂ] ℂ :=
  observer.comp (nativeGpreFiniteTfvdReconstruction q hq0 hq1 S)

/-- Sobre dados produzidos pela analise, o readout visivel e exatamente o
funcional original do estado; a proveniencia nao interfere nem e apagada. -/
@[simp] theorem nativeGpreFiniteTfvdVisibleReadout_analysis
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (observer : CarryVerticalL2 →L[ℂ] ℂ)
    (x : CarryVerticalL2) :
    nativeGpreFiniteTfvdVisibleReadout q hqpos.le hq1 S observer
        (nativeGpreFiniteTfvdAnalysis q S x) =
      observer x := by
  change observer
      (nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S
        (nativeGpreFiniteTfvdAnalysis q S x)) = observer x
  rw [nativeGpreFiniteTfvdReconstruction_analysis q hqpos hq1 S]

/-- Orbita linear de posto um gerada por um estado vertical fixo. -/
def nativeGpreFiniteTfvdVisibleOrbit (x : CarryVerticalL2) :
    ℂ →L[ℂ] CarryVerticalL2 :=
  ContinuousLinearMap.toSpanSingleton ℂ x

@[simp] theorem nativeGpreFiniteTfvdVisibleOrbit_apply
    (x : CarryVerticalL2) (z : ℂ) :
    nativeGpreFiniteTfvdVisibleOrbit x z = z • x := rfl

/-- Fluxo escalar obtido passando a orbita primeiro pela analise enriquecida e
entao pelo observador visivel. -/
def nativeGpreFiniteTfvdVisibleFlux
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (observer : CarryVerticalL2 →L[ℂ] ℂ)
    (x : CarryVerticalL2) : ℂ →L[ℂ] ℂ :=
  (nativeGpreFiniteTfvdVisibleReadout q hq0 hq1 S observer).comp
    ((nativeGpreFiniteTfvdAnalysis q S).comp
      (nativeGpreFiniteTfvdVisibleOrbit x))

/-- A compressao possui coeficiente literal `observer x`. -/
@[simp] theorem nativeGpreFiniteTfvdVisibleFlux_apply
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (observer : CarryVerticalL2 →L[ℂ] ℂ)
    (x : CarryVerticalL2) (z : ℂ) :
    nativeGpreFiniteTfvdVisibleFlux q hqpos.le hq1 S observer x z =
      z * observer x := by
  change
    nativeGpreFiniteTfvdVisibleReadout q hqpos.le hq1 S observer
      (nativeGpreFiniteTfvdAnalysis q S (z • x)) = z * observer x
  rw [nativeGpreFiniteTfvdVisibleReadout_analysis
    q hqpos hq1 S observer (z • x)]
  simpa using observer.map_smul z x

/-- Pencil regular da compressao visivel de uma orbita nativa. -/
def nativeGpreFiniteTfvdVisibleBoundaryPencil
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (observer : CarryVerticalL2 →L[ℂ] ℂ)
    (x : CarryVerticalL2) :
    RegularLinearBoundaryPencil ℂ ℂ where
  valueEquiv := LinearEquiv.refl ℂ ℂ
  fluxTrace :=
    (nativeGpreFiniteTfvdVisibleFlux q hq0 hq1 S observer x).toLinearMap

@[simp] theorem nativeGpreFiniteTfvdVisibleBoundaryLinearization_apply
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (observer : CarryVerticalL2 →L[ℂ] ℂ)
    (x : CarryVerticalL2) (z : ℂ) :
    (nativeGpreFiniteTfvdVisibleBoundaryPencil
      q hqpos.le hq1 S observer x).linearization z =
        z * observer x := by
  exact nativeGpreFiniteTfvdVisibleFlux_apply
    q hqpos hq1 S observer x z

/-- Os valores caracteristicos da compressao sao exatamente o readout visivel
na orbita escolhida. -/
theorem nativeGpreFiniteTfvdVisible_isCharacteristicValue_iff
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (observer : CarryVerticalL2 →L[ℂ] ℂ)
    (x : CarryVerticalL2) (lambda : ℂ) :
    (nativeGpreFiniteTfvdVisibleBoundaryPencil
        q hqpos.le hq1 S observer x).toLinearBoundaryPencil.IsCharacteristicValue
          lambda ↔
      lambda = observer x := by
  constructor
  · rintro ⟨z, hz, hzero⟩
    change z ≠ 0 at hz
    change
      nativeGpreFiniteTfvdVisibleFlux q hqpos.le hq1 S observer x z -
        lambda * z = 0 at hzero
    rw [nativeGpreFiniteTfvdVisibleFlux_apply
      q hqpos hq1 S observer x z] at hzero
    have hmul : (observer x - lambda) * z = 0 := by
      calc
        (observer x - lambda) * z =
            z * observer x - lambda * z := by ring
        _ = 0 := hzero
    have hcoeff : observer x - lambda = 0 :=
      (mul_eq_zero.mp hmul).resolve_right hz
    exact (sub_eq_zero.mp hcoeff).symm
  · intro hlambda
    subst lambda
    refine ⟨1, ?_, ?_⟩
    · change (1 : ℂ) ≠ 0
      norm_num
    · change
        nativeGpreFiniteTfvdVisibleFlux q hqpos.le hq1 S observer x 1 -
          observer x * 1 = 0
      rw [nativeGpreFiniteTfvdVisibleFlux_apply
        q hqpos hq1 S observer x 1]
      ring

/-- Zero e caracteristico exatamente quando a compressao visivel fecha. -/
theorem nativeGpreFiniteTfvdVisible_zeroCharacteristic_iff
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (observer : CarryVerticalL2 →L[ℂ] ℂ)
    (x : CarryVerticalL2) :
    (nativeGpreFiniteTfvdVisibleBoundaryPencil
        q hqpos.le hq1 S observer x).toLinearBoundaryPencil.IsCharacteristicValue
          0 ↔
      observer x = 0 := by
  simpa [eq_comm] using
    (nativeGpreFiniteTfvdVisible_isCharacteristicValue_iff
      q hqpos hq1 S observer x 0)

/-- A relacao escalar comprimida e fechada. -/
theorem nativeGpreFiniteTfvdVisibleBoundaryRelation_isClosed
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (observer : CarryVerticalL2 →L[ℂ] ℂ)
    (x : CarryVerticalL2) :
    IsClosed
      (((nativeGpreFiniteTfvdVisibleBoundaryPencil
        q hqpos.le hq1 S observer x).toLinearBoundaryPencil.relation :
          Set (ℂ × ℂ))) :=
  ((nativeGpreFiniteTfvdVisibleBoundaryPencil
    q hqpos.le hq1 S observer x).toLinearBoundaryPencil.relation).closed_of_finiteDimensional

end

end CPFormal.Analytic.Cp
