import CPFormal.Analytic.CpFiniteTfvdAngularGreenIntertwiner
import CPFormal.Analytic.CpGenuineTiltProductRule

/-!
# Identificacao TFVD do bracket Genuine e do remainder do carrier

O retorno TFVD enriquecido recupera tres gradientes consecutivos de cada
bloco canonico. A segunda diferenca Genuine no centro seguinte e exatamente

`terceira aresta - segunda aresta`.

Isso fornece uma identificacao que nao define o bracket, o tilt nem o
remainder por residual: o lado TFVD e uma leitura linear independente das
coordenadas retornadas, enquanto o lado Genuine ja existe como segunda
diferenca do monomio completo. Compondo essa leitura com a regra discreta de
produto, obtemos bloco a bloco

`retorno TFVD Genuine = tilt critico ponderado + remainder do carrier`.

O mesmo enunciado e somado em cortes finitos. Num zero Genuine, a leitura
TFVD total converge a `-1`; nenhuma parcela e apagada e nenhuma saturacao e
postulada nesta etapa.
-/

open scoped BigOperators Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-!
## Leitura local do retorno enriquecido
-/

/-- Leitura Genuine do retorno TFVD enriquecido. Depois de decodificar as
tres arestas, ela toma a diferenca orientada `dormant - second`. -/
def enrichedTfvdGenuineBracketReadout
    (kappa omega : ℂ) (z : EnrichedAngularTfvdCoordinate) : ℂ :=
  let edges := enrichedAngularTfvdDecode kappa omega z
  edges.dormant - edges.second

/-- A leitura Genuine escrita diretamente nos tres canais armazenados:
proveniencia dormente, through-flow e bracket-flow. -/
theorem enrichedTfvdGenuineBracketReadout_eq_channels
    (kappa omega : ℂ) (z : EnrichedAngularTfvdCoordinate) :
    enrichedTfvdGenuineBracketReadout kappa omega z =
      z.dormantEdge + kappa * z.visible.throughFlow / 2 -
        kappa * z.visible.bracketFlow / (2 * omega) := by
  unfold enrichedTfvdGenuineBracketReadout enrichedAngularTfvdDecode
    tfvdDecode
  dsimp
  ring

/-- Codificar e retornar tres arestas recupera exatamente a diferenca entre
a terceira e a segunda. -/
theorem enrichedTfvdGenuineBracketReadout_encode
    (block : ℕ) {kappa omega : ℂ}
    (hkappa : kappa ≠ 0) (homega : omega ≠ 0)
    (first second dormant : ℂ) :
    enrichedTfvdGenuineBracketReadout kappa omega
        (enrichedAngularTfvdEncode block kappa omega
          first second dormant) =
      dormant - second := by
  unfold enrichedTfvdGenuineBracketReadout
  rw [enrichedAngularTfvdDecode_encode block hkappa homega]

/-- No bloco Dirichlet canonico, a leitura do retorno TFVD enriquecido e
literalmente o bracket Genuine `p = 3` no mesmo centro. -/
theorem enrichedTfvdGenuineBracketReadout_canonical
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (m : ℕ) (homega : omega m ≠ 0) (s : ℂ) :
    enrichedTfvdGenuineBracketReadout kappa (omega m)
        (canonicalEnrichedAngularTfvdCoordinate kappa omega m s) =
      realCpSaturatedBracket 3 m s := by
  unfold canonicalEnrichedAngularTfvdCoordinate
  rw [enrichedTfvdGenuineBracketReadout_encode m hkappa homega,
    realCpSaturatedBracket_three_eq_values]
  simp [positiveDirichletGradient]
  ring

/-!
## Identificacao com o tilt e o carrier
-/

/-- Identidade local principal: a leitura TFVD do mesmo bloco e exatamente
o tilt critico ponderado mais os canais de curvatura e cruzamento do carrier. -/
theorem enrichedTfvdGenuineBracketReadout_canonical_eq_weightedTilt_add_carrierRemainder
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (m : ℕ) (homega : omega m ≠ 0) (s : ℂ) :
    enrichedTfvdGenuineBracketReadout kappa (omega m)
        (canonicalEnrichedAngularTfvdCoordinate kappa omega m s) =
      canonicalCriticalWeightedTiltBlock m s +
        canonicalCriticalCarrierRemainderBlock m s := by
  rw [enrichedTfvdGenuineBracketReadout_canonical
      hkappa omega m homega s,
    realCpSaturatedBracket_three_eq_weightedTilt_add_carrierRemainder]

/-- Forma resolvida da identificacao: o remainder do carrier preexistente e
a leitura TFVD retornada menos o tilt critico ponderado. -/
theorem canonicalCriticalCarrierRemainderBlock_eq_tfvdReadout_sub_weightedTilt
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (m : ℕ) (homega : omega m ≠ 0) (s : ℂ) :
    canonicalCriticalCarrierRemainderBlock m s =
      enrichedTfvdGenuineBracketReadout kappa (omega m)
          (canonicalEnrichedAngularTfvdCoordinate kappa omega m s) -
        canonicalCriticalWeightedTiltBlock m s := by
  rw [enrichedTfvdGenuineBracketReadout_canonical_eq_weightedTilt_add_carrierRemainder
      hkappa omega m homega s]
  ring

/-!
## Colagem finita
-/

/-- Sintese finita da leitura Genuine somente depois de retornar cada trio
TFVD enriquecido. -/
def finiteEnrichedTfvdGenuineBracketReadout
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ)
    (port : ℕ → EnrichedAngularTfvdCoordinate) : ℂ :=
  ∑ m ∈ Finset.range M,
    enrichedTfvdGenuineBracketReadout kappa (omega m) (port m)

/-- A colagem dos retornos TFVD canonicos recupera exatamente o traco finito
da carta bracketada Genuine. -/
theorem finiteEnrichedTfvdGenuineBracketReadout_canonical
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    finiteEnrichedTfvdGenuineBracketReadout M kappa omega
        (canonicalEnrichedAngularTfvdCoordinate kappa omega · s) =
      finiteCanonicalBracketTrace M s := by
  unfold finiteEnrichedTfvdGenuineBracketReadout finiteCanonicalBracketTrace
  apply Finset.sum_congr rfl
  intro m hm
  exact enrichedTfvdGenuineBracketReadout_canonical
    hkappa omega m (homega m) s

/-- A mesma colagem, agora aberta nos dois canais `same-s`. -/
theorem finiteEnrichedTfvdGenuineBracketReadout_canonical_eq_weightedTilt_add_carrierRemainder
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    finiteEnrichedTfvdGenuineBracketReadout M kappa omega
        (canonicalEnrichedAngularTfvdCoordinate kappa omega · s) =
      finiteCanonicalCriticalWeightedTiltTrace M s +
        finiteCanonicalCriticalCarrierRemainderTrace M s := by
  rw [finiteEnrichedTfvdGenuineBracketReadout_canonical
      M hkappa omega homega s,
    finiteCanonicalBracketTrace_eq_weightedTilt_add_carrierRemainder]

/-- Identificacao finita resolvida do remainder: retorno TFVD menos tilt. -/
theorem finiteCanonicalCriticalCarrierRemainderTrace_eq_tfvdReadout_sub_weightedTilt
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    finiteCanonicalCriticalCarrierRemainderTrace M s =
      finiteEnrichedTfvdGenuineBracketReadout M kappa omega
          (canonicalEnrichedAngularTfvdCoordinate kappa omega · s) -
        finiteCanonicalCriticalWeightedTiltTrace M s := by
  rw [finiteEnrichedTfvdGenuineBracketReadout_canonical_eq_weightedTilt_add_carrierRemainder
      M hkappa omega homega s]
  ring

/-- Transporte honesto de um zero Genuine ao retorno TFVD: no strip, o
traco dos blocos retornados converge a `-1`. A decomposicao mostra que esse
valor ainda contem juntos tilt e remainder do carrier. -/
theorem finiteEnrichedTfvdGenuineBracketReadout_tendsto_neg_one_of_genuine_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) :
    Tendsto
      (fun M : ℕ ↦
        finiteEnrichedTfvdGenuineBracketReadout M kappa omega
          (canonicalEnrichedAngularTfvdCoordinate kappa omega · s))
      atTop (nhds (-1)) := by
  have hledger :=
    finiteCanonicalWeightedTilt_add_carrierRemainder_tendsto_neg_one_of_genuine_zero
      hs hzero
  have hpoint : ∀ M : ℕ,
      finiteEnrichedTfvdGenuineBracketReadout M kappa omega
          (canonicalEnrichedAngularTfvdCoordinate kappa omega · s) =
        finiteCanonicalCriticalWeightedTiltTrace M s +
          finiteCanonicalCriticalCarrierRemainderTrace M s := by
    intro M
    exact
      finiteEnrichedTfvdGenuineBracketReadout_canonical_eq_weightedTilt_add_carrierRemainder
        M hkappa omega homega s
  simpa only [hpoint] using hledger

end

end CPFormal.Analytic.Cp
