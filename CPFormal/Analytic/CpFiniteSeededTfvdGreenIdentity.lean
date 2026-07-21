import CPFormal.Analytic.CpSeededTfvdSameSBoundary
import CPFormal.Analytic.CpFiniteGenuineTfvdProvenanceGluing

/-!
# Identidade finita entre a porta TFVD semeada e o Green Genuine

Este modulo fecha o checkpoint 0.49. Os quatro termos da identidade sao
definidos antes de qualquer igualdade:

* a forma de bordo `same-s` retornada pela TFVD enriquecida;
* o fluxo Green Genuine complexo, acoplado ao bordo bracketado alinhado;
* o endpoint movel, escrito diretamente como carta finita menos endpoint;
* o defeito de proveniencia, construido por trocas de pernas locais.

O defeito nao e definido como a diferenca entre os outros tres termos. Cada
celula possui quatro canais explicitos: transporte da aresta direita,
transporte do jet esquerdo, transporte da aresta esquerda e transporte do jet
direito. O terceiro residuo do bloco aparece separadamente como compensacao
Green dormente. Portanto nenhuma coordenada e descartada e nenhuma soma entre
blocos distintos e introduzida.

A identidade final e finita e exata:

`BoundaryForm = CoupledGreenFlux + MovingEndpoint + ProvenanceDefect`.

Sua parte real usa literalmente o fluxo radial assinado ja existente. Este
arquivo nao afirma que o defeito de proveniencia desaparece, nem usa uma
hipotese de zero Genuine para forcar a linha critica.
-/

open scoped BigOperators Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-!
## Os quatro objetos independentes
-/

/-- Forma de bordo canonica da porta TFVD semeada. As duas celulas de cada
trio sao formadas antes da soma em `m`. -/
def finiteCanonicalSeededTfvdSameSBoundaryForm
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) : ℂ :=
  finiteCanonicalEnrichedTfvdSameSBoundaryTrace M kappa omega s

/-- Versao complexa do fluxo Genuine acoplado. Sua parte real recupera a
definicao assinada preexistente. -/
def finiteCanonicalTfvdCoupledGenuineGreenFlux
    (p M : ℕ) (s : ℂ) : ℂ :=
  finiteOrientedGenuineCpGreenFlux p (3 * M) s +
    finiteCanonicalAngularBracketCoupledBoundary M s

/-- Endpoint movel da porta semeada: carta finita menos endpoint Green
exterior, nos cutoffs alinhados `M` e `3M`. -/
def finiteCanonicalSeededTfvdGreenMovingEndpoint
    (M : ℕ) (s : ℂ) : ℂ :=
  finiteBracketedDirichletChart 3 M s -
    finiteReflectedOuterEndpoint (3 * M) s

/-- Quatro trocas de pernas que levam uma celula `same-s` a uma aresta Green
refletida. Cada campo e uma diferenca de coordenadas tipadas, e nao o residual
de uma identidade escalar. -/
structure TfvdSameSGreenLegChannels where
  rightValueTransport : ℂ
  jetLeftTransport : ℂ
  leftValueTransport : ℂ
  jetRightTransport : ℂ

/-- Totalizacao de uma unica troca de pernas somente depois de preservar seus
quatro canais. -/
def TfvdSameSGreenLegChannels.total
    (x : TfvdSameSGreenLegChannels) : ℂ :=
  x.rightValueTransport + x.jetLeftTransport +
    x.leftValueTransport + x.jetRightTransport

/-- Canais canonicos que comparam uma celula formada pelas arestas `n,n+1`
com a aresta Green de proveniencia `n`. -/
def canonicalTfvdSameSGreenLegChannels
    (p n : ℕ) (s : ℂ) : TfvdSameSGreenLegChannels :=
  {
    rightValueTransport :=
      (positiveDirichletGradient s (n + 1) -
          (starRingEnd ℂ) (positiveDirichletGradient s n)) *
        positiveLogDirichletGradient s n
    jetLeftTransport :=
      (starRingEnd ℂ) (positiveDirichletGradient s n) *
        (positiveLogDirichletGradient s n -
          phaseNormalizedCpBlockGradient p (reflectedParameter s) n)
    leftValueTransport :=
      -(positiveDirichletGradient s n -
          (starRingEnd ℂ) (phaseNormalizedCpBlockGradient p s n)) *
        positiveLogDirichletGradient s (n + 1)
    jetRightTransport :=
      -(starRingEnd ℂ) (phaseNormalizedCpBlockGradient p s n) *
        (positiveLogDirichletGradient s (n + 1) -
          positiveDirichletGradient (reflectedParameter s) n)
  }

/-- Proveniencia de um bloco angular completo. As duas celulas usam os
residuos `0,1`; a terceira entrada conserva explicitamente o residuo dormente
`2` exigido pela diagonal Green. -/
structure TfvdSameSGreenProvenanceChannels where
  visibleLegs : TfvdSameSGreenLegChannels
  dormantLegs : TfvdSameSGreenLegChannels
  dormantGreenCompensation : ℂ

/-- Totalizacao dos canais de proveniencia de um bloco completo. -/
def TfvdSameSGreenProvenanceChannels.total
    (x : TfvdSameSGreenProvenanceChannels) : ℂ :=
  x.visibleLegs.total + x.dormantLegs.total +
    x.dormantGreenCompensation

/-- Canais canonicos de proveniencia do bloco `m`. A compensacao dormente e
a terceira aresta Green com a orientacao exigida pela colagem. -/
def canonicalTfvdSameSGreenProvenanceChannels
    (p m : ℕ) (s : ℂ) : TfvdSameSGreenProvenanceChannels :=
  {
    visibleLegs := canonicalTfvdSameSGreenLegChannels p (3 * m) s
    dormantLegs := canonicalTfvdSameSGreenLegChannels p (3 * m + 1) s
    dormantGreenCompensation :=
      -canonicalOrientedCpGreenEdge p (3 * m + 2) s
  }

/-- Defeito de proveniencia finito, definido bloco a bloco pelos canais
anteriores. Nao ha termo off-diagonal nem diferenca entre totais globais. -/
def finiteCanonicalTfvdSameSGreenProvenanceDefect
    (p M : ℕ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.range M,
    (canonicalTfvdSameSGreenProvenanceChannels p m s).total

/-!
## Identificacoes locais
-/

/-- Celula `same-s` canonica formada por dois gradientes consecutivos. -/
def canonicalSameSEdgeBoundaryWedge
    (n : ℕ) (s : ℂ) : ℂ :=
  sameSEdgeBoundaryWedge
    (positiveDirichletGradient s n)
    (positiveDirichletGradient s (n + 1))
    (positiveLogDirichletGradient s n)
    (positiveLogDirichletGradient s (n + 1))

/-- A troca das quatro pernas e uma identidade local exata. O lado de
proveniencia ja estava definido antes deste teorema. -/
theorem canonicalSameSEdgeBoundaryWedge_eq_green_add_legChannels
    (p n : ℕ) (s : ℂ) :
    canonicalSameSEdgeBoundaryWedge n s =
      canonicalOrientedCpGreenEdge p n s +
        (canonicalTfvdSameSGreenLegChannels p n s).total := by
  unfold canonicalSameSEdgeBoundaryWedge sameSEdgeBoundaryWedge
    canonicalTfvdSameSGreenLegChannels
    TfvdSameSGreenLegChannels.total
    canonicalOrientedCpGreenEdge
  rw [tfvdReflectedGreenWedge_canonicalCpGreenCoordinates]
  ring

/-- O par de celulas retornado no bloco `m` coincide com as duas celulas
canonicas consecutivas `3m` e `3m+1`. -/
theorem canonicalEnrichedTfvdSameSBoundaryCells_total_eq_edges
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (m : ℕ) (homega : omega m ≠ 0) (s : ℂ) :
    (canonicalEnrichedTfvdSameSBoundaryCells
        kappa omega m s).total =
      canonicalSameSEdgeBoundaryWedge (3 * m) s +
        canonicalSameSEdgeBoundaryWedge (3 * m + 1) s := by
  rw [canonicalEnrichedTfvdSameSBoundaryCells_eq_gradients
    hkappa omega m homega s]
  rfl

/-!
## Colagem finita
-/

/-- A forma TFVD e a diagonal Green Genuine mais os canais locais de
proveniencia. O reagrupamento usa exatamente os tres residuos de cada bloco. -/
theorem finiteCanonicalSeededTfvdSameSBoundaryForm_eq_green_add_provenance
    (p : ℕ) (hp : Nat.Prime p)
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    finiteCanonicalSeededTfvdSameSBoundaryForm M kappa omega s =
      finiteOrientedGenuineCpGreenFlux p (3 * M) s +
        finiteCanonicalTfvdSameSGreenProvenanceDefect p M s := by
  unfold finiteCanonicalSeededTfvdSameSBoundaryForm
    finiteCanonicalEnrichedTfvdSameSBoundaryTrace
  calc
    (∑ m ∈ Finset.range M,
        (canonicalEnrichedTfvdSameSBoundaryCells
          kappa omega m s).total) =
        ∑ m ∈ Finset.range M,
          ((canonicalOrientedCpGreenEdge p (3 * m) s +
              canonicalOrientedCpGreenEdge p (3 * m + 1) s +
              canonicalOrientedCpGreenEdge p (3 * m + 2) s) +
            (canonicalTfvdSameSGreenProvenanceChannels p m s).total) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [canonicalEnrichedTfvdSameSBoundaryCells_total_eq_edges
          hkappa omega m (homega m) s,
        canonicalSameSEdgeBoundaryWedge_eq_green_add_legChannels,
        canonicalSameSEdgeBoundaryWedge_eq_green_add_legChannels]
      unfold canonicalTfvdSameSGreenProvenanceChannels
        TfvdSameSGreenProvenanceChannels.total
      dsimp
      ring
    _ =
        (∑ m ∈ Finset.range M,
          (canonicalOrientedCpGreenEdge p (3 * m) s +
            canonicalOrientedCpGreenEdge p (3 * m + 1) s +
            canonicalOrientedCpGreenEdge p (3 * m + 2) s)) +
          finiteCanonicalTfvdSameSGreenProvenanceDefect p M s := by
      rw [Finset.sum_add_distrib]
      rfl
    _ =
        (∑ n ∈ Finset.range (3 * M),
          canonicalOrientedCpGreenEdge p n s) +
          finiteCanonicalTfvdSameSGreenProvenanceDefect p M s := by
      apply congrArg
        (fun z : ℂ ↦
          z + finiteCanonicalTfvdSameSGreenProvenanceDefect p M s)
      exact sum_range_threeBlocks_eq_range
        (fun n ↦ canonicalOrientedCpGreenEdge p n s) M
    _ = finiteOrientedCpGreenFlux p (3 * M) s +
          finiteCanonicalTfvdSameSGreenProvenanceDefect p M s := by
      rw [sum_range_canonicalOrientedCpGreenEdge_eq_finiteOrientedCpGreenFlux]
    _ = finiteOrientedGenuineCpGreenFlux p (3 * M) s +
          finiteCanonicalTfvdSameSGreenProvenanceDefect p M s := by
      rw [finiteOrientedGenuineCpGreenFlux_eq_finiteOrientedCpGreenFlux
        p (3 * M) hp s]

/-- O endpoint movel e o negativo literal do bordo bracketado alinhado. -/
theorem finiteCanonicalSeededTfvdGreenMovingEndpoint_eq_neg_boundary
    (M : ℕ) (s : ℂ) :
    finiteCanonicalSeededTfvdGreenMovingEndpoint M s =
      -finiteCanonicalAngularBracketCoupledBoundary M s := by
  rw [finiteCanonicalAngularBracketCoupledBoundary_eq_outer_sub_finiteChart]
  unfold finiteCanonicalSeededTfvdGreenMovingEndpoint
  ring

/-- A parte real da versao complexa e exatamente o fluxo Genuine acoplado
assinado que possui a fatoracao radial por `criticalDisplacement`. -/
theorem finiteCanonicalTfvdCoupledGenuineGreenFlux_re
    (p M : ℕ) (s : ℂ) :
    (finiteCanonicalTfvdCoupledGenuineGreenFlux p M s).re =
      finiteCanonicalAngularBracketCoupledGenuineGreenFlux p M s := by
  unfold finiteCanonicalTfvdCoupledGenuineGreenFlux
    finiteCanonicalAngularBracketCoupledGenuineGreenFlux
    finiteCanonicalAngularBracketCoupledSignedBoundary
  simp only [Complex.add_re]

/-- Identidade finita TFVD--Green do checkpoint 0.49. Todos os termos do lado
direito foram definidos antes do enunciado, e o defeito preserva seus canais
locais em vez de ser definido pela igualdade. -/
theorem finiteCanonicalSeededTfvdGreen_identity
    (p : ℕ) (hp : Nat.Prime p)
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    finiteCanonicalSeededTfvdSameSBoundaryForm M kappa omega s =
      finiteCanonicalTfvdCoupledGenuineGreenFlux p M s +
        finiteCanonicalSeededTfvdGreenMovingEndpoint M s +
          finiteCanonicalTfvdSameSGreenProvenanceDefect p M s := by
  rw [finiteCanonicalSeededTfvdSameSBoundaryForm_eq_green_add_provenance
    p hp M hkappa omega homega s]
  unfold finiteCanonicalTfvdCoupledGenuineGreenFlux
  rw [finiteCanonicalSeededTfvdGreenMovingEndpoint_eq_neg_boundary]
  ring

/-- Projecao radial assinada da mesma identidade. Esta e a forma indicada
pelos testes numericos: nenhuma estimativa em modulo do carrier e usada. -/
theorem finiteCanonicalSeededTfvdGreen_signed_identity
    (p : ℕ) (hp : Nat.Prime p)
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    (finiteCanonicalSeededTfvdSameSBoundaryForm M kappa omega s).re =
      finiteCanonicalAngularBracketCoupledGenuineGreenFlux p M s +
        (finiteCanonicalSeededTfvdGreenMovingEndpoint M s).re +
          (finiteCanonicalTfvdSameSGreenProvenanceDefect p M s).re := by
  have h := congrArg Complex.re
    (finiteCanonicalSeededTfvdGreen_identity
      p hp M hkappa omega homega s)
  simp only [Complex.add_re] at h
  rw [finiteCanonicalTfvdCoupledGenuineGreenFlux_re] at h
  exact h

/-- O endpoint da 0.49 ja herda o fechamento Genuine certificado. Isto nao
implica, por si so, o fechamento da forma bilinear de bordo. -/
theorem finiteCanonicalSeededTfvdGreenMovingEndpoint_tendsto_zero_of_genuine_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
      (fun M : ℕ ↦ finiteCanonicalSeededTfvdGreenMovingEndpoint M s)
      atTop (nhds 0) := by
  have hboundary :=
    finiteCanonicalAngularBracketCoupledBoundary_tendsto_zero_of_genuine_zero
      hs hzero
  have hneg := hboundary.neg
  simpa only
      [finiteCanonicalSeededTfvdGreenMovingEndpoint_eq_neg_boundary,
        neg_zero] using hneg

/-!
## Interface unica do checkpoint analitico seguinte
-/

/-- Observavel radial que resta depois de separar o defeito de proveniencia
local da forma de bordo. O nome nao afirma que ele desaparece. -/
def finiteCanonicalSeededTfvdGreenRadialClosureObservable
    (p M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) : ℝ :=
  (finiteCanonicalSeededTfvdSameSBoundaryForm M kappa omega s).re -
    (finiteCanonicalTfvdSameSGreenProvenanceDefect p M s).re

/-- Forma resolvida do ledger assinado: o observavel radial e fluxo acoplado
mais endpoint movel. -/
theorem finiteCanonicalSeededTfvdGreenRadialClosureObservable_eq_flux_add_endpoint
    (p : ℕ) (hp : Nat.Prime p)
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    finiteCanonicalSeededTfvdGreenRadialClosureObservable
        p M kappa omega s =
      finiteCanonicalAngularBracketCoupledGenuineGreenFlux p M s +
        (finiteCanonicalSeededTfvdGreenMovingEndpoint M s).re := by
  unfold finiteCanonicalSeededTfvdGreenRadialClosureObservable
  rw [finiteCanonicalSeededTfvdGreen_signed_identity
    p hp M hkappa omega homega s]
  ring

/-- Proposicao pontual e unica a ser fechada na 0.50. -/
def SeededTfvdGreenRadialClosureAt
    (p : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) : Prop :=
  Tendsto
    (fun M : ℕ ↦
      finiteCanonicalSeededTfvdGreenRadialClosureObservable
        p M kappa omega s)
    atTop (nhds 0)

/-- Num zero Genuine, o novo gate radial e equivalente ao fechamento do
fluxo Green acoplado. O endpoint ja foi eliminado pelo teorema anterior;
nenhuma anulacao da forma de bordo ou da proveniencia e presumida. -/
theorem seededTfvdGreenRadialClosureAt_iff_coupledGreenFlux_tendsto_zero_of_genuine_zero
    (p : ℕ) (hp : Nat.Prime p)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    SeededTfvdGreenRadialClosureAt p kappa omega s ↔
      Tendsto
        (fun M : ℕ ↦
          finiteCanonicalAngularBracketCoupledGenuineGreenFlux p M s)
        atTop (nhds 0) := by
  have hendpointComplex :=
    finiteCanonicalSeededTfvdGreenMovingEndpoint_tendsto_zero_of_genuine_zero
      hs hzero
  have hendpoint :
      Tendsto
        (fun M : ℕ ↦
          (finiteCanonicalSeededTfvdGreenMovingEndpoint M s).re)
        atTop (nhds 0) := by
    have hreal :=
      Complex.continuous_re.continuousAt.tendsto.comp hendpointComplex
    simpa [Function.comp_def] using hreal
  have hpoint : ∀ M : ℕ,
      finiteCanonicalSeededTfvdGreenRadialClosureObservable
          p M kappa omega s =
        finiteCanonicalAngularBracketCoupledGenuineGreenFlux p M s +
          (finiteCanonicalSeededTfvdGreenMovingEndpoint M s).re := by
    intro M
    exact
      finiteCanonicalSeededTfvdGreenRadialClosureObservable_eq_flux_add_endpoint
        p hp M hkappa omega homega s
  constructor
  · intro hclosure
    have hdiff := hclosure.sub hendpoint
    have hfun :
        (fun M : ℕ ↦
          finiteCanonicalAngularBracketCoupledGenuineGreenFlux p M s) =
        (fun M : ℕ ↦
          finiteCanonicalSeededTfvdGreenRadialClosureObservable
              p M kappa omega s -
            (finiteCanonicalSeededTfvdGreenMovingEndpoint M s).re) := by
      funext M
      rw [hpoint M]
      ring
    rw [hfun]
    simpa using hdiff
  · intro hflux
    have hsum := hflux.add hendpoint
    simpa only [hpoint] using hsum

end

end CPFormal.Analytic.Cp
