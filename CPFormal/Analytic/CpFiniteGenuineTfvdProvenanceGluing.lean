import CPFormal.Analytic.CpGenuineGreenIntertwiner
import CPFormal.Analytic.CpFiniteTfvdLogJetResidualCutoff

/-!
# Colagem finita Genuine--TFVD com proveniencia

Este modulo coloca no mesmo cutoff as cadeias que ate aqui apareciam em
linguagens diferentes. Um bloco angular possui tres arestas, portanto um
cutoff de `M` blocos corresponde exatamente ao cutoff Green `3 * M`.

A colagem preserva todos os termos, sem declarar que um defeito desaparece:

* o retorno TFVD enriquecido transporta qualquer trio horizontal ao portador
  Green;
* o wedge log-jet enriquecido, somado em `M` blocos, e o fluxo de vertices
  nas primeiras `3 * M` arestas;
* esse fluxo e o Green Genuine mais o defeito log-jet--Green explicito;
* o bordo bracketado usa o mesmo cutoff angular `M` e o cutoff Green `3 * M`.

O teorema final e um ledger finito exato. Ele certifica a colagem global das
pecas ja formalizadas, mas nao postula a anulacao do defeito nem a linha
critica.
-/

open scoped BigOperators Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-!
## Intertwiner enriquecido para uma entrada arbitraria
-/

/--
Transporte Green de um portador TFVD enriquecido arbitrario. Diferentemente
do mapa canonico anterior, esta definicao consome de fato a entrada `z`.
-/
def enrichedAngularTfvdCoordinateToCpGreenTriple
    (p : ℕ) (kappa omega s : ℂ)
    (z : EnrichedAngularTfvdCoordinate) : CpGreenTfvdTriple :=
  let edges := enrichedAngularTfvdDecode kappa omega z
  {
    first := cpGreenTfvdCoordinateFromHorizontal p (3 * z.visible.block) s
      edges.first
    second := cpGreenTfvdCoordinateFromHorizontal p
      (3 * z.visible.block + 1) s edges.second
    dormant := cpGreenTfvdCoordinateFromHorizontal p
      (3 * z.visible.block + 2) s edges.dormant
  }

/-- O transporte de uma codificacao recuperavel usa as tres arestas dadas. -/
theorem enrichedAngularTfvdCoordinateToCpGreenTriple_encode
    (p block : ℕ) {kappa omega : ℂ}
    (hkappa : kappa ≠ 0) (homega : omega ≠ 0)
    (first second dormant s : ℂ) :
    enrichedAngularTfvdCoordinateToCpGreenTriple p kappa omega s
        (enrichedAngularTfvdEncode block kappa omega
          first second dormant) =
      ({
        first := cpGreenTfvdCoordinateFromHorizontal p (3 * block) s first
        second := cpGreenTfvdCoordinateFromHorizontal p
          (3 * block + 1) s second
        dormant := cpGreenTfvdCoordinateFromHorizontal p
          (3 * block + 2) s dormant
      } : CpGreenTfvdTriple) := by
  unfold enrichedAngularTfvdCoordinateToCpGreenTriple
  rw [enrichedAngularTfvdDecode_encode block hkappa homega
    first second dormant]
  simp only [enrichedAngularTfvdEncode_visible_block]

/-- Na entrada aritmetica canonica, o transporte e o trio Green canonico. -/
theorem enrichedAngularTfvdCoordinateToCpGreenTriple_eq_canonical
    (p : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (m : ℕ) (homega : omega m ≠ 0) (s : ℂ) :
    enrichedAngularTfvdCoordinateToCpGreenTriple p kappa (omega m) s
        (canonicalEnrichedAngularTfvdCoordinate kappa omega m s) =
      canonicalCpGreenTfvdTriple p m s := by
  unfold canonicalEnrichedAngularTfvdCoordinate
  rw [enrichedAngularTfvdCoordinateToCpGreenTriple_encode
    p m hkappa homega]
  apply CpGreenTfvdTriple.ext
  · exact cpGreenTfvdCoordinateFromHorizontal_eq_canonical
      p (3 * m) s
  · exact cpGreenTfvdCoordinateFromHorizontal_eq_canonical
      p (3 * m + 1) s
  · exact cpGreenTfvdCoordinateFromHorizontal_eq_canonical
      p (3 * m + 2) s

/-!
## Cutoff comum para bordo e Green
-/

/--
Bordo bracketado alinhado: `M` trios angulares correspondem a `3 * M`
arestas Green, enquanto a carta canonica possui `M` blocos.
-/
def finiteCanonicalAngularBracketCoupledBoundary
    (M : ℕ) (s : ℂ) : ℂ :=
  finiteReflectedBoundary (3 * M) s - finiteCanonicalBracketTrace M s

/-- Forma independente do bordo alinhado: endpoint externo menos carta. -/
theorem finiteCanonicalAngularBracketCoupledBoundary_eq_outer_sub_finiteChart
    (M : ℕ) (s : ℂ) :
    finiteCanonicalAngularBracketCoupledBoundary M s =
      finiteReflectedOuterEndpoint (3 * M) s -
        finiteBracketedDirichletChart 3 M s := by
  rw [finiteBracketedDirichletChart_three_eq_inner_add_trace]
  unfold finiteCanonicalAngularBracketCoupledBoundary finiteReflectedBoundary
  ring

/-- O bordo alinhado converge para o negativo da carta bracketada. -/
theorem finiteCanonicalAngularBracketCoupledBoundary_tendsto_neg_chart
    {s : ℂ} (hs : -1 < s.re) :
    Tendsto
      (fun M : ℕ ↦ finiteCanonicalAngularBracketCoupledBoundary M s)
      atTop (nhds (-bracketedDirichletChart 3 s)) := by
  have hthree : Tendsto (fun M : ℕ ↦ 3 * M) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with M hM
    omega
  have houter := (finiteReflectedOuterEndpoint_tendsto_zero s).comp hthree
  have hchart := finiteBracketedDirichletChart_tendsto
    3 (by norm_num) hs
  simpa only
      [finiteCanonicalAngularBracketCoupledBoundary_eq_outer_sub_finiteChart,
        zero_sub, Function.comp_apply] using houter.sub hchart

/-- Num zero Genuine, tambem o bordo com cutoffs alinhados desaparece. -/
theorem finiteCanonicalAngularBracketCoupledBoundary_tendsto_zero_of_genuine_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
      (fun M : ℕ ↦ finiteCanonicalAngularBracketCoupledBoundary M s)
      atTop (nhds 0) := by
  have hchart : bracketedDirichletChart 3 s = 0 :=
    (bracketedDirichletChart_zero_iff_genuineContinuation_zero
      3 (by norm_num) (by norm_num) hs).2 hzero
  simpa [hchart] using
    (finiteCanonicalAngularBracketCoupledBoundary_tendsto_neg_chart
      (s := s) (by linarith [hs.1]))

/-- Parte real assinada do bordo alinhado. -/
def finiteCanonicalAngularBracketCoupledSignedBoundary
    (M : ℕ) (s : ℂ) : ℝ :=
  (finiteCanonicalAngularBracketCoupledBoundary M s).re

/-- A parte real do bordo alinhado tambem desaparece num zero Genuine. -/
theorem finiteCanonicalAngularBracketCoupledSignedBoundary_tendsto_zero_of_genuine_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
      (fun M : ℕ ↦
        finiteCanonicalAngularBracketCoupledSignedBoundary M s)
      atTop (nhds 0) := by
  have hcomplex :=
    finiteCanonicalAngularBracketCoupledBoundary_tendsto_zero_of_genuine_zero
      hs hzero
  have hreal := Complex.continuous_re.continuousAt.tendsto.comp hcomplex
  simpa [finiteCanonicalAngularBracketCoupledSignedBoundary,
    Function.comp_def] using hreal

/-- Fluxo Genuine e bordo bracketado no mesmo cutoff angular. -/
def finiteCanonicalAngularBracketCoupledGenuineGreenFlux
    (p M : ℕ) (s : ℂ) : ℝ :=
  (finiteOrientedGenuineCpGreenFlux p (3 * M) s).re +
    finiteCanonicalAngularBracketCoupledSignedBoundary M s

/-!
## Traco TFVD enriquecido e ledger global
-/

/-- Soma dos wedges enriquecidos nos primeiros `M` blocos completos. -/
def finiteCanonicalEnrichedTfvdReflectedLogJetWedgeTrace
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.range M,
    TfvdWedgeTriple.total
      (canonicalEnrichedTfvdReflectedLogJetWedgeTriple
        kappa omega m s)

/--
O traco TFVD enriquecido e exatamente o fluxo consecutivo das primeiras
`3 * M` arestas; a proveniencia dormente nao se perde na sintese.
-/
theorem finiteCanonicalEnrichedTfvdReflectedLogJetWedgeTrace_eq_vertexFlux
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    (M : ℕ) (s : ℂ) :
    finiteCanonicalEnrichedTfvdReflectedLogJetWedgeTrace
        M kappa omega s =
      finiteReflectedLogJetVertexFlux (3 * M) s := by
  unfold finiteCanonicalEnrichedTfvdReflectedLogJetWedgeTrace
  calc
    (∑ m ∈ Finset.range M,
        TfvdWedgeTriple.total
          (canonicalEnrichedTfvdReflectedLogJetWedgeTriple
            kappa omega m s)) =
        ∑ m ∈ Finset.range M,
          (reflectedLogJetVertexFlux (3 * m) s +
            reflectedLogJetVertexFlux (3 * m + 1) s +
            reflectedLogJetVertexFlux (3 * m + 2) s) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [canonicalEnrichedTfvdReflectedLogJetWedgeTriple_eq_canonical
        hkappa omega m (homega m) s]
      unfold TfvdWedgeTriple.total canonicalReflectedLogJetWedgeTriple
      rw [canonicalReflectedLogJetEdgeWedge_eq_vertexFlux,
        canonicalReflectedLogJetEdgeWedge_eq_vertexFlux,
        canonicalReflectedLogJetEdgeWedge_eq_vertexFlux]
    _ = finiteReflectedLogJetVertexFlux (3 * M) s := by
      simpa [finiteReflectedLogJetVertexFlux] using
        (sum_range_threeBlocks_eq_range
          (fun n ↦ reflectedLogJetVertexFlux n s) M)

/-- A mesma colagem exibe exatamente o cutoff movel e o bulk cruzado. -/
theorem finiteCanonicalEnrichedTfvdReflectedLogJetWedgeTrace_eq_cutoff_add_crossBulk
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    (M : ℕ) (s : ℂ) :
    finiteCanonicalEnrichedTfvdReflectedLogJetWedgeTrace
        M kappa omega s =
      reflectedLogJetMovingCutoff (3 * M) s +
        finiteReflectedLogJetCrossBulk (3 * M) s := by
  rw [finiteCanonicalEnrichedTfvdReflectedLogJetWedgeTrace_eq_vertexFlux
      hkappa omega homega M s,
    finiteReflectedLogJetVertexFlux_eq_cutoff_add_crossBulk]

/--
Colagem TFVD--Genuine exata: o traco enriquecido e Green Genuine mais o
defeito log-jet--Green, ambos no mesmo conjunto de `3 * M` arestas.
-/
theorem finiteCanonicalEnrichedTfvdReflectedLogJetWedgeTrace_eq_genuineGreen_add_defect
    (p : ℕ) (hp : Nat.Prime p)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    (M : ℕ) (s : ℂ) :
    finiteCanonicalEnrichedTfvdReflectedLogJetWedgeTrace
        M kappa omega s =
      finiteOrientedGenuineCpGreenFlux p (3 * M) s +
        finiteCanonicalLogJetGreenDefectTrace p M s := by
  rw [finiteCanonicalEnrichedTfvdReflectedLogJetWedgeTrace_eq_vertexFlux
      hkappa omega homega M s,
    finiteOrientedGenuineCpGreenFlux_eq_finiteOrientedCpGreenFlux
      p (3 * M) hp s,
    finiteCanonicalLogJetGreenDefectTrace_eq_vertex_sub_green]
  ring

/--
Ledger global finito. Depois de descontar o defeito explicitamente tipado e
recolocar o bordo bracketado, sobra exatamente o fluxo Genuine acoplado.
-/
theorem finiteCanonicalAngularBracketCoupledGenuineGreenFlux_eq_enrichedLedger
    (p : ℕ) (hp : Nat.Prime p)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    (M : ℕ) (s : ℂ) :
    finiteCanonicalAngularBracketCoupledGenuineGreenFlux p M s =
      (finiteCanonicalEnrichedTfvdReflectedLogJetWedgeTrace
          M kappa omega s -
        finiteCanonicalLogJetGreenDefectTrace p M s +
        finiteCanonicalAngularBracketCoupledBoundary M s).re := by
  rw [finiteCanonicalEnrichedTfvdReflectedLogJetWedgeTrace_eq_genuineGreen_add_defect
    p hp hkappa omega homega M s]
  unfold finiteCanonicalAngularBracketCoupledGenuineGreenFlux
    finiteCanonicalAngularBracketCoupledSignedBoundary
  simp only [Complex.add_re, Complex.sub_re]
  ring

/-!
## Teste exato da linha critica

O ledger acima permite formular o gate final sem uma ponte abstrata. Primeiro
reabrimos o fluxo alinhado na direcao radial. Depois provamos que, num zero
Genuine, o fechamento do proprio ledger e equivalente a `re(s) = 1 / 2`.
-/

/-- O fluxo alinhado conserva a fatoracao radial Green nas `3 * M` arestas. -/
theorem finiteCanonicalAngularBracketCoupledGenuineGreenFlux_eq_radialDifference_mul_pairing
    (p M : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    finiteCanonicalAngularBracketCoupledGenuineGreenFlux p M s =
      cpRadialDifference p (criticalDisplacement s.re) *
          (finiteReflectedGradientPairing (3 * M) s).re +
        finiteCanonicalAngularBracketCoupledSignedBoundary M s := by
  unfold finiteCanonicalAngularBracketCoupledGenuineGreenFlux
  rw [finiteOrientedGenuineCpGreenFlux_eq_finiteOrientedCpGreenFlux
      p (3 * M) hp s,
    finiteOrientedCpGreenFlux_eq_radialDifference_mul_pairing
      p (3 * M) hp s]
  simp [Complex.mul_re]

/--
Se o fluxo alinhado fecha num zero Genuine, a positividade Green obriga o
coeficiente radial a zerar.
-/
theorem criticalDisplacement_eq_zero_of_alignedGenuineGreenFlux_tendsto_zero
    (p : ℕ) (hp : Nat.Prime p) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hflux :
      Tendsto
        (fun M : ℕ ↦
          finiteCanonicalAngularBracketCoupledGenuineGreenFlux p M s)
        atTop (nhds 0)) :
    criticalDisplacement s.re = 0 := by
  let c : ℝ := cpRadialDifference p (criticalDisplacement s.re)
  let pairingRe : ℕ → ℝ :=
    fun M ↦ (finiteReflectedGradientPairing (3 * M) s).re
  have hboundary :=
    finiteCanonicalAngularBracketCoupledSignedBoundary_tendsto_zero_of_genuine_zero
      hs hzero
  have hproduct :
      Tendsto (fun M : ℕ ↦ c * pairingRe M) atTop (nhds 0) := by
    have hsub := hflux.sub hboundary
    have hfun :
        (fun M : ℕ ↦ c * pairingRe M) =
          (fun M : ℕ ↦
            finiteCanonicalAngularBracketCoupledGenuineGreenFlux p M s -
              finiteCanonicalAngularBracketCoupledSignedBoundary M s) := by
      funext M
      dsimp [c, pairingRe]
      rw [finiteCanonicalAngularBracketCoupledGenuineGreenFlux_eq_radialDifference_mul_pairing
        p M hp s]
      ring
    rw [hfun]
    simpa using hsub
  have hpositive : 0 < pairingRe 1 := by
    dsimp [pairingRe]
    exact finiteReflectedGradientPairing_re_pos (by norm_num) hs
  have hgreenMonotone := finiteReflectedGradientPairing_re_monotone hs
  have hbound : ∀ᶠ M in atTop, pairingRe 1 ≤ pairingRe M :=
    eventually_atTop.2 ⟨1, fun M hM ↦ hgreenMonotone (by omega)⟩
  have hc : c = 0 :=
    constant_eq_zero_of_tendsto_mul_of_eventually_pos_lower_bound
      hpositive hbound hproduct
  have hfactor := cpRadialDifference_eq_two_mul_delta_mul_cofactor
    p (criticalDisplacement s.re)
  have hcofactor := cpRadialCofactor_pos
    p hp (criticalDisplacement s.re)
  dsimp [c] at hc
  nlinarith

/-- Na linha critica, o termo radial zera e resta o bordo ja fechado. -/
theorem alignedGenuineGreenFlux_tendsto_zero_of_criticalDisplacement
    (p : ℕ) (hp : Nat.Prime p) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hcritical : criticalDisplacement s.re = 0) :
    Tendsto
      (fun M : ℕ ↦
        finiteCanonicalAngularBracketCoupledGenuineGreenFlux p M s)
      atTop (nhds 0) := by
  have hboundary :=
    finiteCanonicalAngularBracketCoupledSignedBoundary_tendsto_zero_of_genuine_zero
      hs hzero
  have hpoint : ∀ M : ℕ,
      finiteCanonicalAngularBracketCoupledGenuineGreenFlux p M s =
        finiteCanonicalAngularBracketCoupledSignedBoundary M s := by
    intro M
    rw [finiteCanonicalAngularBracketCoupledGenuineGreenFlux_eq_radialDifference_mul_pairing
      p M hp s, hcritical]
    simp [cpRadialDifference]
  simpa only [hpoint] using hboundary

/--
Resposta kernel-checked do teste global: num zero Genuine, fechar o ledger
TFVD--log-jet--Green--bordo e exatamente o mesmo que estar na linha critica.
-/
theorem enrichedLedger_tendsto_zero_iff_re_eq_half_of_genuine_zero
    (p : ℕ) (hp : Nat.Prime p)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
        (fun M : ℕ ↦
          (finiteCanonicalEnrichedTfvdReflectedLogJetWedgeTrace
              M kappa omega s -
            finiteCanonicalLogJetGreenDefectTrace p M s +
            finiteCanonicalAngularBracketCoupledBoundary M s).re)
        atTop (nhds 0) ↔
      s.re = (1 : ℝ) / 2 := by
  constructor
  · intro hledger
    have hflux :
        Tendsto
          (fun M : ℕ ↦
            finiteCanonicalAngularBracketCoupledGenuineGreenFlux p M s)
          atTop (nhds 0) :=
      hledger.congr' (Eventually.of_forall fun M ↦
        (finiteCanonicalAngularBracketCoupledGenuineGreenFlux_eq_enrichedLedger
          p hp hkappa omega homega M s).symm)
    have hcritical :=
      criticalDisplacement_eq_zero_of_alignedGenuineGreenFlux_tendsto_zero
        p hp hs hzero hflux
    unfold criticalDisplacement at hcritical
    linarith
  · intro hre
    have hcritical : criticalDisplacement s.re = 0 := by
      unfold criticalDisplacement
      linarith
    have hflux :=
      alignedGenuineGreenFlux_tendsto_zero_of_criticalDisplacement
        p hp hs hzero hcritical
    exact hflux.congr' (Eventually.of_forall fun M ↦
      finiteCanonicalAngularBracketCoupledGenuineGreenFlux_eq_enrichedLedger
        p hp hkappa omega homega M s)

/-- Forma implicativa: o fechamento concreto do ledger implica a meia reta. -/
theorem genuine_zero_implies_re_eq_half_of_enrichedLedger_tendsto_zero
    (p : ℕ) (hp : Nat.Prime p)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hledger :
      Tendsto
        (fun M : ℕ ↦
          (finiteCanonicalEnrichedTfvdReflectedLogJetWedgeTrace
              M kappa omega s -
            finiteCanonicalLogJetGreenDefectTrace p M s +
            finiteCanonicalAngularBracketCoupledBoundary M s).re)
        atTop (nhds 0)) :
    s.re = (1 : ℝ) / 2 :=
  (enrichedLedger_tendsto_zero_iff_re_eq_half_of_genuine_zero
    p hp hkappa omega homega hs hzero).mp hledger

end

end CPFormal.Analytic.Cp
