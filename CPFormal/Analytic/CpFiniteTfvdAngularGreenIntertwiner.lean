import CPFormal.Analytic.CpFinitePortWronskian

/-!
# Intertwiner TFVD angular--Green e proveniencia dormente

A porta angular canonica trabalha em blocos de tres gradientes com pesos
residuais 1, 2 e 0. A coordenada TFVD anterior preserva exatamente os dois
gradientes visiveis pelo readout. Este modulo determina o alcance exato
dessa informacao.

Primeiro, os dois gradientes retidos sao transportados ao portador Green
canonico sem erro. Depois, um witness puramente tipado prova que nenhum mapa
universal do par TFVD ordinario/log-jet pode reconstruir uma terceira aresta
arbitraria que nunca entrou em suas entradas.

A correcao minima e guardar essa aresta dormente como proveniencia. O
portador enriquecido continua produzindo literalmente os mesmos blocos Phi
e Psi, mas passa a transportar o trio Green canonico completo bloco a bloco.
Nenhum limite, zero Genuine ou cancelamento off-diagonal e usado aqui.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-- As tres arestas recuperadas de um bloco angular completo. -/
structure TfvdThreeEdges where
  first : ℂ
  second : ℂ
  dormant : ℂ

/-- TFVD visivel acrescido somente da aresta de peso angular zero. -/
structure EnrichedAngularTfvdCoordinate where
  visible : TfvdCoordinate
  dormantEdge : ℂ

/-- Codificacao minima de um bloco angular de tres arestas. -/
def enrichedAngularTfvdEncode
    (block : ℕ) (kappa omega first second dormant : ℂ) :
    EnrichedAngularTfvdCoordinate :=
  {
    visible := tfvdEncode block kappa omega first second
    dormantEdge := dormant
  }

/-- Retorno das duas arestas TFVD junto da proveniencia dormente. -/
def enrichedAngularTfvdDecode
    (kappa omega : ℂ) (z : EnrichedAngularTfvdCoordinate) :
    TfvdThreeEdges :=
  let pair := tfvdDecode kappa omega z.visible
  {
    first := pair.1
    second := pair.2
    dormant := z.dormantEdge
  }

/-- O enriquecimento nao altera o indice do bloco visivel. -/
@[simp] theorem enrichedAngularTfvdEncode_visible_block
    (block : ℕ) (kappa omega first second dormant : ℂ) :
    (enrichedAngularTfvdEncode block kappa omega
      first second dormant).visible.block = block := rfl

/-- A nova coordenada guarda literalmente a aresta dormente. -/
@[simp] theorem enrichedAngularTfvdEncode_dormantEdge
    (block : ℕ) (kappa omega first second dormant : ℂ) :
    (enrichedAngularTfvdEncode block kappa omega
      first second dormant).dormantEdge = dormant := rfl

/-- O retorno enriquecido recupera exatamente as tres arestas. -/
theorem enrichedAngularTfvdDecode_encode
    (block : ℕ) {kappa omega : ℂ}
    (hkappa : kappa ≠ 0) (homega : omega ≠ 0)
    (first second dormant : ℂ) :
    enrichedAngularTfvdDecode kappa omega
        (enrichedAngularTfvdEncode block kappa omega
          first second dormant) =
      { first := first, second := second, dormant := dormant } := by
  unfold enrichedAngularTfvdDecode enrichedAngularTfvdEncode
  rw [tfvdDecode_encode block hkappa homega first second]

/-- Bloco Dirichlet enriquecido com a terceira aresta de residuo 2 mod 3. -/
def canonicalEnrichedAngularTfvdCoordinate
    (kappa : ℂ) (omega : ℕ → ℂ) (m : ℕ) (s : ℂ) :
    EnrichedAngularTfvdCoordinate :=
  enrichedAngularTfvdEncode m kappa (omega m)
    (positiveDirichletGradient s (3 * m))
    (positiveDirichletGradient s (3 * m + 1))
    (positiveDirichletGradient s (3 * m + 2))

/-- Bloco log-jet enriquecido com sua terceira aresta. -/
def canonicalEnrichedLogJetTfvdCoordinate
    (kappa : ℂ) (omega : ℕ → ℂ) (m : ℕ) (s : ℂ) :
    EnrichedAngularTfvdCoordinate :=
  enrichedAngularTfvdEncode m kappa (omega m)
    (positiveLogDirichletGradient s (3 * m))
    (positiveLogDirichletGradient s (3 * m + 1))
    (positiveLogDirichletGradient s (3 * m + 2))

/-- Esquecer a aresta dormente recupera definicionalmente a porta Phi. -/
@[simp] theorem canonicalEnrichedAngularTfvdCoordinate_visible
    (kappa : ℂ) (omega : ℕ → ℂ) (m : ℕ) (s : ℂ) :
    (canonicalEnrichedAngularTfvdCoordinate kappa omega m s).visible =
      canonicalAngularTfvdCoordinate kappa omega m s := rfl

/-- Esquecer a aresta dormente recupera definicionalmente a porta Psi. -/
@[simp] theorem canonicalEnrichedLogJetTfvdCoordinate_visible
    (kappa : ℂ) (omega : ℕ → ℂ) (m : ℕ) (s : ℂ) :
    (canonicalEnrichedLogJetTfvdCoordinate kappa omega m s).visible =
      canonicalLogJetTfvdCoordinate kappa omega m s := rfl

/-- O readout enriquecido continua sendo exatamente o bloco de Phi. -/
theorem tfvdAngularReadout_canonicalEnrichedAngularCoordinate
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (m : ℕ) (homega : omega m ≠ 0) (s : ℂ) :
    tfvdAngularReadout kappa (omega m)
        (canonicalEnrichedAngularTfvdCoordinate
          kappa omega m s).visible =
      canonicalAngularGradientBlock m s := by
  rw [canonicalEnrichedAngularTfvdCoordinate_visible]
  exact tfvdAngularReadout_canonicalAngularCoordinate
    hkappa omega m homega s

/-- O readout enriquecido continua sendo exatamente o bloco de Psi. -/
theorem tfvdAngularReadout_canonicalEnrichedLogJetCoordinate
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (m : ℕ) (homega : omega m ≠ 0) (s : ℂ) :
    tfvdAngularReadout kappa (omega m)
        (canonicalEnrichedLogJetTfvdCoordinate
          kappa omega m s).visible =
      canonicalAngularLogJetBlock m s := by
  rw [canonicalEnrichedLogJetTfvdCoordinate_visible]
  exact tfvdAngularReadout_canonicalLogJetCoordinate
    hkappa omega m homega s

/-!
O par TFVD atual nunca recebe a terceira aresta. O witness abaixo e
informacional: mantendo literalmente as mesmas duas coordenadas de entrada,
a saida exigida pode ser 0 ou 1. Logo nao existe decodificador universal da
aresta dormente a partir do portador atual, mesmo oferecendo juntos os
registros ordinario e log-jet.
-/
theorem no_universalDormantEdgeDecoder_from_currentTfvdPair :
    ¬ ∃ decoder : TfvdCoordinate × TfvdCoordinate → ℂ,
      ∀ (block : ℕ)
        (first second logFirst logSecond dormant : ℂ),
        decoder
          (tfvdEncode block tfvdHaarScale 1 first second,
            tfvdEncode block tfvdHaarScale 1 logFirst logSecond) =
          dormant := by
  rintro ⟨decoder, hdecoder⟩
  have hzero := hdecoder 0 0 0 0 0 0
  have hone := hdecoder 0 0 0 0 0 1
  have hfalse : (0 : ℂ) = 1 := hzero.symm.trans hone
  norm_num at hfalse

/-- Construcao do portador Green a partir de um gradiente horizontal dado. -/
def cpGreenTfvdCoordinateFromHorizontal
    (p n : ℕ) (s horizontal : ℂ) : TfvdCoordinate :=
  tfvdEncode n tfvdHaarScale 1
    (cpPhaseNormalizer p s * natDirichletTerm s p * horizontal)
    horizontal

/-- Para o gradiente aritmetico real, a construcao e o portador Green canonico. -/
theorem cpGreenTfvdCoordinateFromHorizontal_eq_canonical
    (p n : ℕ) (s : ℂ) :
    cpGreenTfvdCoordinateFromHorizontal p n s
        (positiveDirichletGradient s n) =
      canonicalCpGreenTfvdCoordinate p n s := by
  unfold cpGreenTfvdCoordinateFromHorizontal
    canonicalCpGreenTfvdCoordinate phaseNormalizedCpBlockGradient
  rw [cpBlockGradient_eq_eigenvalue_mul]
  simp only [mul_assoc]

/-- O retorno da porta angular atual recupera suas duas arestas visiveis. -/
theorem tfvdDecode_canonicalAngularTfvdCoordinate
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (m : ℕ) (homega : omega m ≠ 0) (s : ℂ) :
    tfvdDecode kappa (omega m)
        (canonicalAngularTfvdCoordinate kappa omega m s) =
      (positiveDirichletGradient s (3 * m),
        positiveDirichletGradient s (3 * m + 1)) := by
  unfold canonicalAngularTfvdCoordinate
  exact tfvdDecode_encode m hkappa homega
    (positiveDirichletGradient s (3 * m))
    (positiveDirichletGradient s (3 * m + 1))

/-- Transporte do primeiro registro visivel ao Green. -/
def angularTfvdToCpGreenFirst
    (p : ℕ) (kappa : ℂ) (omega : ℕ → ℂ)
    (m : ℕ) (s : ℂ) : TfvdCoordinate :=
  cpGreenTfvdCoordinateFromHorizontal p (3 * m) s
    (tfvdDecode kappa (omega m)
      (canonicalAngularTfvdCoordinate kappa omega m s)).1

/-- Transporte do segundo registro visivel ao Green. -/
def angularTfvdToCpGreenSecond
    (p : ℕ) (kappa : ℂ) (omega : ℕ → ℂ)
    (m : ℕ) (s : ℂ) : TfvdCoordinate :=
  cpGreenTfvdCoordinateFromHorizontal p (3 * m + 1) s
    (tfvdDecode kappa (omega m)
      (canonicalAngularTfvdCoordinate kappa omega m s)).2

/-- O primeiro registro transportado e exatamente o Green canonico. -/
theorem angularTfvdToCpGreenFirst_eq_canonical
    (p : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (m : ℕ) (homega : omega m ≠ 0) (s : ℂ) :
    angularTfvdToCpGreenFirst p kappa omega m s =
      canonicalCpGreenTfvdCoordinate p (3 * m) s := by
  unfold angularTfvdToCpGreenFirst
  rw [tfvdDecode_canonicalAngularTfvdCoordinate
    hkappa omega m homega s]
  exact cpGreenTfvdCoordinateFromHorizontal_eq_canonical
    p (3 * m) s

/-- O segundo registro transportado e exatamente o Green canonico. -/
theorem angularTfvdToCpGreenSecond_eq_canonical
    (p : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (m : ℕ) (homega : omega m ≠ 0) (s : ℂ) :
    angularTfvdToCpGreenSecond p kappa omega m s =
      canonicalCpGreenTfvdCoordinate p (3 * m + 1) s := by
  unfold angularTfvdToCpGreenSecond
  rw [tfvdDecode_canonicalAngularTfvdCoordinate
    hkappa omega m homega s]
  exact cpGreenTfvdCoordinateFromHorizontal_eq_canonical
    p (3 * m + 1) s

/-- A proveniencia enriquecida transporta a terceira aresta ao Green. -/
def enrichedAngularTfvdToCpGreenDormant
    (p : ℕ) (kappa : ℂ) (omega : ℕ → ℂ)
    (m : ℕ) (s : ℂ) : TfvdCoordinate :=
  cpGreenTfvdCoordinateFromHorizontal p (3 * m + 2) s
    (canonicalEnrichedAngularTfvdCoordinate
      kappa omega m s).dormantEdge

/-- O registro dormente transportado e exatamente o terceiro Green canonico. -/
theorem enrichedAngularTfvdToCpGreenDormant_eq_canonical
    (p : ℕ) (kappa : ℂ) (omega : ℕ → ℂ)
    (m : ℕ) (s : ℂ) :
    enrichedAngularTfvdToCpGreenDormant p kappa omega m s =
      canonicalCpGreenTfvdCoordinate p (3 * m + 2) s := by
  unfold enrichedAngularTfvdToCpGreenDormant
    canonicalEnrichedAngularTfvdCoordinate
    enrichedAngularTfvdEncode
  exact cpGreenTfvdCoordinateFromHorizontal_eq_canonical
    p (3 * m + 2) s

/-- Trio de coordenadas Green produzido por um bloco angular enriquecido. -/
structure CpGreenTfvdTriple where
  first : TfvdCoordinate
  second : TfvdCoordinate
  dormant : TfvdCoordinate
/-- Extensionalidade explicita do trio Green tipado. -/
theorem CpGreenTfvdTriple.ext
    {x y : CpGreenTfvdTriple}
    (hfirst : x.first = y.first)
    (hsecond : x.second = y.second)
    (hdormant : x.dormant = y.dormant) :
    x = y := by
  cases x
  cases y
  simp_all

/-- Intertwiner local completo depois do enriquecimento minimo. -/
def enrichedAngularTfvdToCpGreenTriple
    (p : ℕ) (kappa : ℂ) (omega : ℕ → ℂ)
    (m : ℕ) (s : ℂ) : CpGreenTfvdTriple :=
  {
    first := angularTfvdToCpGreenFirst p kappa omega m s
    second := angularTfvdToCpGreenSecond p kappa omega m s
    dormant :=
      enrichedAngularTfvdToCpGreenDormant p kappa omega m s
  }

/-- O trio Green canonico nos tres residuos do bloco angular. -/
def canonicalCpGreenTfvdTriple
    (p m : ℕ) (s : ℂ) : CpGreenTfvdTriple :=
  {
    first := canonicalCpGreenTfvdCoordinate p (3 * m) s
    second := canonicalCpGreenTfvdCoordinate p (3 * m + 1) s
    dormant := canonicalCpGreenTfvdCoordinate p (3 * m + 2) s
  }

/--
Teorema central do checkpoint: o enriquecimento por uma unica aresta produz
o trio Green canonico inteiro, bloco por bloco.
-/
theorem enrichedAngularTfvdToCpGreenTriple_eq_canonical
    (p : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (m : ℕ) (homega : omega m ≠ 0) (s : ℂ) :
    enrichedAngularTfvdToCpGreenTriple p kappa omega m s =
      canonicalCpGreenTfvdTriple p m s := by
  apply CpGreenTfvdTriple.ext
  · exact angularTfvdToCpGreenFirst_eq_canonical
      p hkappa omega m homega s
  · exact angularTfvdToCpGreenSecond_eq_canonical
      p hkappa omega m homega s
  · exact enrichedAngularTfvdToCpGreenDormant_eq_canonical
      p kappa omega m s

end

end CPFormal.Analytic.Cp
