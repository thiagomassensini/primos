import CPFormal.Analytic.CpTfvdGenuineCarryIdentification

/-!
# Porta Genuine TFVD semeada e forma de bordo `same-s`

Este modulo fecha o checkpoint 0.48 em duas camadas finitas independentes.

Primeiro, a semente canonica `1` e colocada no mesmo objeto tipado que a
familia de blocos TFVD enriquecidos. O readout Genuine desse portador e
literalmente a carta bracketada finita. Consequentemente, num zero Genuine
no strip, o readout semeado converge a zero.

Depois definimos a forma de bordo `same-s` antes de qualquer sintese escalar.
Dois estados enriquecidos sao retornados a seus tres gradientes
`(first, second, dormant)`. A forma conserva separadamente os determinantes
orientados das duas celulas consecutivas

`(first, second)` e `(second, dormant)`.

A primeira celula tambem e identificada com o wedge simplético dos canais
`throughFlow/bracketFlow` da valvula. Portanto a forma nao e definida como
residual de uma igualdade Green. Este arquivo nao afirma ainda uma identidade
TFVD--Green nem o desaparecimento assintotico de sua forma de bordo; esses sao
os gates separados dos checkpoints seguintes.
-/

open scoped BigOperators Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-!
## Porta enriquecida com semente preservada
-/

/-- Uma familia de blocos TFVD enriquecidos junto de sua semente exterior. -/
structure SeededEnrichedTfvdPort where
  seed : ℂ
  blocks : ℕ → EnrichedAngularTfvdCoordinate

/-- Readout Genuine finito: a semente e somada somente depois de retornar e
ler separadamente os primeiros `M` blocos. -/
def finiteSeededEnrichedTfvdGenuineReadout
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ)
    (port : SeededEnrichedTfvdPort) : ℂ :=
  port.seed +
    finiteEnrichedTfvdGenuineBracketReadout
      M kappa omega port.blocks

/-- Porta Genuine canonica: semente `1` e os trios de gradientes ordinarios. -/
def canonicalSeededEnrichedTfvdGenuinePort
    (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) :
    SeededEnrichedTfvdPort :=
  {
    seed := 1
    blocks := fun m ↦
      canonicalEnrichedAngularTfvdCoordinate kappa omega m s
  }

/-- Porta log-jet canonica: a semente e `log(1) = 0`. -/
def canonicalSeededEnrichedTfvdLogJetPort
    (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) :
    SeededEnrichedTfvdPort :=
  {
    seed := 0
    blocks := fun m ↦
      canonicalEnrichedLogJetTfvdCoordinate kappa omega m s
  }

@[simp] theorem canonicalSeededEnrichedTfvdGenuinePort_seed
    (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) :
    (canonicalSeededEnrichedTfvdGenuinePort kappa omega s).seed = 1 := rfl

@[simp] theorem canonicalSeededEnrichedTfvdLogJetPort_seed
    (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) :
    (canonicalSeededEnrichedTfvdLogJetPort kappa omega s).seed = 0 := rfl

/-- O readout da porta Genuine semeada e exatamente a carta bracketada
finita canonica, sem termo residual. -/
theorem finiteSeededEnrichedTfvdGenuineReadout_canonical
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    finiteSeededEnrichedTfvdGenuineReadout M kappa omega
        (canonicalSeededEnrichedTfvdGenuinePort kappa omega s) =
      finiteBracketedDirichletChart 3 M s := by
  unfold finiteSeededEnrichedTfvdGenuineReadout
    canonicalSeededEnrichedTfvdGenuinePort
  dsimp
  rw [finiteEnrichedTfvdGenuineBracketReadout_canonical
    M hkappa omega homega s]
  exact (finiteBracketedDirichletChart_three_eq_one_add_trace M s).symm

/-- Fechamento Genuine-first da porta semeada: um zero do Genuine no strip
faz seu readout TFVD convergir a zero. -/
theorem finiteSeededEnrichedTfvdGenuineReadout_tendsto_zero_of_genuine_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) :
    Tendsto
      (fun M : ℕ ↦
        finiteSeededEnrichedTfvdGenuineReadout M kappa omega
          (canonicalSeededEnrichedTfvdGenuinePort kappa omega s))
      atTop (nhds 0) := by
  have hchart : bracketedDirichletChart 3 s = 0 :=
    (bracketedDirichletChart_zero_iff_genuineContinuation_zero
      3 (by norm_num) (by norm_num) hs).2 hzero
  have hfinite := finiteBracketedDirichletChart_tendsto
    3 (by norm_num) (show -1 < s.re by linarith [hs.1])
  rw [hchart] at hfinite
  have hpoint : ∀ M : ℕ,
      finiteSeededEnrichedTfvdGenuineReadout M kappa omega
          (canonicalSeededEnrichedTfvdGenuinePort kappa omega s) =
        finiteBracketedDirichletChart 3 M s := by
    intro M
    exact finiteSeededEnrichedTfvdGenuineReadout_canonical
      M hkappa omega homega s
  simpa only [hpoint] using hfinite

/-!
## A perna log-jet passa pela mesma leitura de bracket
-/

/-- No trio log-jet, `dormant - second` e a segunda diferenca log-pesada do
mesmo bloco. -/
theorem enrichedTfvdGenuineBracketReadout_canonicalLogJet
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (m : ℕ) (homega : omega m ≠ 0) (s : ℂ) :
    enrichedTfvdGenuineBracketReadout kappa (omega m)
        (canonicalEnrichedLogJetTfvdCoordinate kappa omega m s) =
      canonicalLogBracketBlock m s := by
  unfold canonicalEnrichedLogJetTfvdCoordinate
  rw [enrichedTfvdGenuineBracketReadout_encode m hkappa homega]
  simp [canonicalLogBracketBlock, positiveLogDirichletGradient]
  ring

/-- A colagem finita dos readouts log-jet recupera sua carta bracketada com
semente zero. -/
theorem finiteSeededEnrichedTfvdGenuineReadout_canonicalLogJet
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    finiteSeededEnrichedTfvdGenuineReadout M kappa omega
        (canonicalSeededEnrichedTfvdLogJetPort kappa omega s) =
      finiteCanonicalLogBracketChart M s := by
  unfold finiteSeededEnrichedTfvdGenuineReadout
    canonicalSeededEnrichedTfvdLogJetPort
    finiteEnrichedTfvdGenuineBracketReadout
    finiteCanonicalLogBracketChart
  dsimp
  apply Finset.sum_congr rfl
  intro m hm
  exact enrichedTfvdGenuineBracketReadout_canonicalLogJet
    hkappa omega m (homega m) s

/-!
## Forma de bordo local nas tres arestas retornadas
-/

/-- Determinante orientado de dois estados sobre uma celula de duas arestas. -/
def sameSEdgeBoundaryWedge
    (left right jetLeft jetRight : ℂ) : ℂ :=
  right * jetLeft - left * jetRight

/-- As duas celulas consecutivas preservadas por um trio de arestas. -/
structure TfvdSameSBoundaryCells where
  visibleCell : ℂ
  dormantCell : ℂ

/-- Extensionalidade explicita do par de celulas de bordo. -/
theorem TfvdSameSBoundaryCells.ext
    {x y : TfvdSameSBoundaryCells}
    (hvisible : x.visibleCell = y.visibleCell)
    (hdormant : x.dormantCell = y.dormantCell) :
    x = y := by
  cases x
  cases y
  simp_all

/-- Sintese das duas celulas somente depois de ambas terem sido preservadas. -/
def TfvdSameSBoundaryCells.total
    (x : TfvdSameSBoundaryCells) : ℂ :=
  x.visibleCell + x.dormantCell

/-- Forma simplética escrita diretamente nos canais nativos de uma valvula. -/
def tfvdSameSChannelBoundaryWedge
    (kappa omega : ℂ) (value jet : TfvdCoordinate) : ℂ :=
  kappa ^ 2 / (2 * omega) *
    (value.throughFlow * jet.bracketFlow -
      value.bracketFlow * jet.throughFlow)

/-- O determinante das arestas retornadas e literalmente o wedge dos canais
`through/bracket`. A igualdade vale por expansao da propria valvula. -/
theorem sameSEdgeBoundaryWedge_decoded_eq_channelWedge
    (kappa omega : ℂ) (value jet : TfvdCoordinate) :
    sameSEdgeBoundaryWedge
        (tfvdDecode kappa omega value).1
        (tfvdDecode kappa omega value).2
        (tfvdDecode kappa omega jet).1
        (tfvdDecode kappa omega jet).2 =
      tfvdSameSChannelBoundaryWedge kappa omega value jet := by
  unfold sameSEdgeBoundaryWedge tfvdDecode
    tfvdSameSChannelBoundaryWedge
  ring

/-- Forma `same-s` no portador enriquecido. As duas portas sao retornadas
antes do pareamento, e as duas celulas adjacentes mantem todas as tres
arestas como coordenadas independentes. -/
def enrichedTfvdSameSBoundaryCells
    (kappa omega : ℂ)
    (value jet : EnrichedAngularTfvdCoordinate) :
    TfvdSameSBoundaryCells :=
  let valueEdges := enrichedAngularTfvdDecode kappa omega value
  let jetEdges := enrichedAngularTfvdDecode kappa omega jet
  {
    visibleCell := sameSEdgeBoundaryWedge
      valueEdges.first valueEdges.second
      jetEdges.first jetEdges.second
    dormantCell := sameSEdgeBoundaryWedge
      valueEdges.second valueEdges.dormant
      jetEdges.second jetEdges.dormant
  }

/-- A primeira celula da forma enriquecida coincide com o wedge simplético
dos canais visiveis da valvula. -/
theorem enrichedTfvdSameSBoundaryCells_visible_eq_channelWedge
    (kappa omega : ℂ)
    (value jet : EnrichedAngularTfvdCoordinate) :
    (enrichedTfvdSameSBoundaryCells kappa omega value jet).visibleCell =
      tfvdSameSChannelBoundaryWedge
        kappa omega value.visible jet.visible := by
  unfold enrichedTfvdSameSBoundaryCells enrichedAngularTfvdDecode
  dsimp
  exact sameSEdgeBoundaryWedge_decoded_eq_channelWedge
    kappa omega value.visible jet.visible

/-- Codificar e retornar dois trios produz os dois determinantes literais,
sem compressao escalar ou termo off-diagonal. -/
theorem enrichedTfvdSameSBoundaryCells_encode
    (block : ℕ) {kappa omega : ℂ}
    (hkappa : kappa ≠ 0) (homega : omega ≠ 0)
    (valueFirst valueSecond valueDormant : ℂ)
    (jetFirst jetSecond jetDormant : ℂ) :
    enrichedTfvdSameSBoundaryCells kappa omega
        (enrichedAngularTfvdEncode block kappa omega
          valueFirst valueSecond valueDormant)
        (enrichedAngularTfvdEncode block kappa omega
          jetFirst jetSecond jetDormant) =
      {
        visibleCell := sameSEdgeBoundaryWedge
          valueFirst valueSecond jetFirst jetSecond
        dormantCell := sameSEdgeBoundaryWedge
          valueSecond valueDormant jetSecond jetDormant
      } := by
  unfold enrichedTfvdSameSBoundaryCells
  rw [enrichedAngularTfvdDecode_encode block hkappa homega,
    enrichedAngularTfvdDecode_encode block hkappa homega]

/-- A forma local e alternada ao trocar suas duas pernas. -/
theorem enrichedTfvdSameSBoundaryCells_swap
    (kappa omega : ℂ)
    (value jet : EnrichedAngularTfvdCoordinate) :
    enrichedTfvdSameSBoundaryCells kappa omega value jet =
      {
        visibleCell :=
          -(enrichedTfvdSameSBoundaryCells
              kappa omega jet value).visibleCell
        dormantCell :=
          -(enrichedTfvdSameSBoundaryCells
              kappa omega jet value).dormantCell
      } := by
  apply TfvdSameSBoundaryCells.ext
  · unfold enrichedTfvdSameSBoundaryCells sameSEdgeBoundaryWedge
    dsimp
    ring
  · unfold enrichedTfvdSameSBoundaryCells sameSEdgeBoundaryWedge
    dsimp
    ring

/-- Em particular, parear uma porta consigo mesma produz zero nas duas
celulas, antes de qualquer soma. -/
theorem enrichedTfvdSameSBoundaryCells_self
    (kappa omega : ℂ) (value : EnrichedAngularTfvdCoordinate) :
    enrichedTfvdSameSBoundaryCells kappa omega value value =
      { visibleCell := 0, dormantCell := 0 } := by
  apply TfvdSameSBoundaryCells.ext
  · unfold enrichedTfvdSameSBoundaryCells sameSEdgeBoundaryWedge
    dsimp
    ring
  · unfold enrichedTfvdSameSBoundaryCells sameSEdgeBoundaryWedge
    dsimp
    ring

/-!
## Especializacao canonica no mesmo parametro `s`
-/

/-- Forma de bordo bloco a bloco entre a porta Genuine e seu log-jet no
mesmo parametro espectral. -/
def canonicalEnrichedTfvdSameSBoundaryCells
    (kappa : ℂ) (omega : ℕ → ℂ) (m : ℕ) (s : ℂ) :
    TfvdSameSBoundaryCells :=
  enrichedTfvdSameSBoundaryCells kappa (omega m)
    (canonicalEnrichedAngularTfvdCoordinate kappa omega m s)
    (canonicalEnrichedLogJetTfvdCoordinate kappa omega m s)

/-- A especializacao canonica conserva os dois determinantes consecutivos
dos gradientes ordinarios e log-pesados. -/
theorem canonicalEnrichedTfvdSameSBoundaryCells_eq_gradients
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (m : ℕ) (homega : omega m ≠ 0) (s : ℂ) :
    canonicalEnrichedTfvdSameSBoundaryCells kappa omega m s =
      {
        visibleCell := sameSEdgeBoundaryWedge
          (positiveDirichletGradient s (3 * m))
          (positiveDirichletGradient s (3 * m + 1))
          (positiveLogDirichletGradient s (3 * m))
          (positiveLogDirichletGradient s (3 * m + 1))
        dormantCell := sameSEdgeBoundaryWedge
          (positiveDirichletGradient s (3 * m + 1))
          (positiveDirichletGradient s (3 * m + 2))
          (positiveLogDirichletGradient s (3 * m + 1))
          (positiveLogDirichletGradient s (3 * m + 2))
      } := by
  unfold canonicalEnrichedTfvdSameSBoundaryCells
    canonicalEnrichedAngularTfvdCoordinate
    canonicalEnrichedLogJetTfvdCoordinate
  exact enrichedTfvdSameSBoundaryCells_encode
    m hkappa homega
    (positiveDirichletGradient s (3 * m))
    (positiveDirichletGradient s (3 * m + 1))
    (positiveDirichletGradient s (3 * m + 2))
    (positiveLogDirichletGradient s (3 * m))
    (positiveLogDirichletGradient s (3 * m + 1))
    (positiveLogDirichletGradient s (3 * m + 2))

/-- Traco finito da forma `same-s`. Cada par de celulas e formado localmente
antes de sua totalizacao e antes da soma sobre blocos. -/
def finiteCanonicalEnrichedTfvdSameSBoundaryTrace
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.range M,
    TfvdSameSBoundaryCells.total
      (canonicalEnrichedTfvdSameSBoundaryCells kappa omega m s)

end

end CPFormal.Analytic.Cp
