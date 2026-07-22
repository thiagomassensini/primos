import CPFormal.Analytic.CpAngularPort

/-!
# Ponte TFVD finita para as portas angulares

Este arquivo introduz somente a mudanca de coordenadas finita da valvula.
Cada coordenada retém seu indice de bloco, seu `through-flow` e seu fluxo de
bracket. Portanto a proveniencia nao e apagada antes da sintese escalar.

Para uma escala nao nula `kappa` e um peso de curvatura nao nulo `omega`, a
valvula envia duas arestas `(left,right)` para

`through = -(left + right) / kappa`,
`bracket = omega * (right - left) / kappa`.

O retorno recupera literalmente as duas arestas. A leitura angular

`(3*kappa/2) * through - (kappa/(2*omega)) * bracket`

e exatamente `-(left + 2*right)`. Aplicada bloco a bloco aos campos de
Dirichlet e log-Dirichlet, ela recupera as portas finitas `Phi_M` e `Psi_M`
ja construidas em `CpAngularPort`.

Essas identidades sao uma ponte tipada e finita. Elas ainda nao identificam
o Wronskiano refletido das portas com o fluxo Green global: essa etapa exige
manter as coordenadas ortogonais durante o pareamento, antes da sintese.
-/

open scoped BigOperators

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Escala de Haar usada na normalizacao TFVD dos documentos. -/
def tfvdHaarScale : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)

/-- A escala de Haar e nao nula. -/
theorem tfvdHaarScale_ne_zero : tfvdHaarScale ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  simp only [tfvdHaarScale, Complex.ofReal_re, Complex.zero_re] at hre
  exact (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne' hre

/-- Uma coordenada enriquecida da valvula, antes da sintese escalar. -/
structure TfvdCoordinate where
  block : ℕ
  throughFlow : ℂ
  bracketFlow : ℂ

/-- Codificacao TFVD de duas arestas, preservando o indice do bloco. -/
def tfvdEncode
    (block : ℕ) (kappa omega left right : ℂ) : TfvdCoordinate :=
  {
    block := block
    throughFlow := -(left + right) / kappa
    bracketFlow := omega * (right - left) / kappa
  }

/-- Retorno local da valvula para as duas arestas originais. -/
def tfvdDecode
    (kappa omega : ℂ) (z : TfvdCoordinate) : ℂ × ℂ :=
  (
    -kappa * z.throughFlow / 2 -
      kappa * z.bracketFlow / (2 * omega),
    -kappa * z.throughFlow / 2 +
      kappa * z.bracketFlow / (2 * omega)
  )

/-- A codificacao nunca apaga a proveniencia do bloco. -/
@[simp] theorem tfvdEncode_block
    (block : ℕ) (kappa omega left right : ℂ) :
    (tfvdEncode block kappa omega left right).block = block := rfl

/-- A valvula local e invertivel para escala e peso nao nulos. -/
theorem tfvdDecode_encode
    (block : ℕ) {kappa omega : ℂ}
    (hkappa : kappa ≠ 0) (homega : omega ≠ 0)
    (left right : ℂ) :
    tfvdDecode kappa omega (tfvdEncode block kappa omega left right) =
      (left, right) := by
  apply Prod.ext
  · dsimp [tfvdDecode, tfvdEncode]
    field_simp [hkappa, homega]
    ring
  · dsimp [tfvdDecode, tfvdEncode]
    field_simp [hkappa, homega]
    ring

/-- Leitura escalar dos dois canais que reproduz os pesos angulares `1,2`. -/
def tfvdAngularReadout
    (kappa omega : ℂ) (z : TfvdCoordinate) : ℂ :=
  3 * kappa * z.throughFlow / 2 -
    kappa * z.bracketFlow / (2 * omega)

/-- A leitura angular e a combinacao `-(left + 2*right)` das arestas retornadas. -/
theorem tfvdAngularReadout_eq_decoded
    (kappa omega : ℂ) (z : TfvdCoordinate) :
    tfvdAngularReadout kappa omega z =
      -((tfvdDecode kappa omega z).1 +
        2 * (tfvdDecode kappa omega z).2) := by
  unfold tfvdAngularReadout tfvdDecode
  ring

/-- A sintese depois da codificacao recupera exatamente os pesos `1,2`. -/
theorem tfvdAngularReadout_encode
    (block : ℕ) {kappa omega : ℂ}
    (hkappa : kappa ≠ 0) (homega : omega ≠ 0)
    (left right : ℂ) :
    tfvdAngularReadout kappa omega
        (tfvdEncode block kappa omega left right) =
      -(left + 2 * right) := by
  rw [tfvdAngularReadout_eq_decoded,
    tfvdDecode_encode block hkappa homega left right]

/-- Coordenada TFVD do bloco angular ordinario. -/
def canonicalAngularTfvdCoordinate
    (kappa : ℂ) (omega : ℕ → ℂ) (m : ℕ) (s : ℂ) :
    TfvdCoordinate :=
  tfvdEncode m kappa (omega m)
    (positiveDirichletGradient s (3 * m))
    (positiveDirichletGradient s (3 * m + 1))

/-- Coordenada TFVD do mesmo bloco aplicada ao campo log-pesado. -/
def canonicalLogJetTfvdCoordinate
    (kappa : ℂ) (omega : ℕ → ℂ) (m : ℕ) (s : ℂ) :
    TfvdCoordinate :=
  tfvdEncode m kappa (omega m)
    (positiveLogDirichletGradient s (3 * m))
    (positiveLogDirichletGradient s (3 * m + 1))

/-- A porta ordinaria preserva o indice de cada bloco. -/
@[simp] theorem canonicalAngularTfvdCoordinate_block
    (kappa : ℂ) (omega : ℕ → ℂ) (m : ℕ) (s : ℂ) :
    (canonicalAngularTfvdCoordinate kappa omega m s).block = m := rfl

/-- A porta log-jet preserva o indice de cada bloco. -/
@[simp] theorem canonicalLogJetTfvdCoordinate_block
    (kappa : ℂ) (omega : ℕ → ℂ) (m : ℕ) (s : ℂ) :
    (canonicalLogJetTfvdCoordinate kappa omega m s).block = m := rfl

/-- A leitura de uma coordenada TFVD ordinaria e o bloco de `Phi`. -/
theorem tfvdAngularReadout_canonicalAngularCoordinate
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (m : ℕ) (homega : omega m ≠ 0) (s : ℂ) :
    tfvdAngularReadout kappa (omega m)
        (canonicalAngularTfvdCoordinate kappa omega m s) =
      canonicalAngularGradientBlock m s := by
  unfold canonicalAngularTfvdCoordinate
  rw [tfvdAngularReadout_encode m hkappa homega]
  exact (canonicalAngularGradientBlock_eq_two_edges m s).symm

/-- A leitura de uma coordenada TFVD log-pesada e o bloco de `Psi`. -/
theorem tfvdAngularReadout_canonicalLogJetCoordinate
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (m : ℕ) (homega : omega m ≠ 0) (s : ℂ) :
    tfvdAngularReadout kappa (omega m)
        (canonicalLogJetTfvdCoordinate kappa omega m s) =
      canonicalAngularLogJetBlock m s := by
  unfold canonicalLogJetTfvdCoordinate
  rw [tfvdAngularReadout_encode m hkappa homega]
  exact (canonicalAngularLogJetBlock_eq_two_edges m s).symm

/-- Sintese finita de uma familia de coordenadas, somente depois de reter os blocos. -/
def finiteTfvdAngularReadout
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ)
    (port : ℕ → TfvdCoordinate) : ℂ :=
  ∑ m ∈ Finset.range M,
    tfvdAngularReadout kappa (omega m) (port m)

/-!
Ponte finita para `Phi`: a sintese do portador enriquecido recupera a porta
angular escalar ja provada equivalente a carta bracketada, com nenhum termo
adicional e para qualquer familia de pesos nao nulos.
-/
theorem finiteTfvdAngularReadout_canonicalAngularPort
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    finiteTfvdAngularReadout M kappa omega
        (canonicalAngularTfvdCoordinate kappa omega · s) =
      finiteCanonicalAngularTrace M s := by
  unfold finiteTfvdAngularReadout finiteCanonicalAngularTrace
  apply Finset.sum_congr rfl
  intro m hm
  exact tfvdAngularReadout_canonicalAngularCoordinate
    hkappa omega m (homega m) s

/-!
Ponte finita para `Psi`: o log-jet escalar e a sintese exata do retorno TFVD
bloco a bloco. A igualdade ocorre antes de qualquer limite ou hipotese de
zero e mantem a proveniencia disponivel no lado esquerdo.
-/
theorem finiteTfvdAngularReadout_canonicalLogJetPort
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    finiteTfvdAngularReadout M kappa omega
        (canonicalLogJetTfvdCoordinate kappa omega · s) =
      finiteCanonicalAngularLogJetTrace M s := by
  unfold finiteTfvdAngularReadout finiteCanonicalAngularLogJetTrace
  apply Finset.sum_congr rfl
  intro m hm
  exact tfvdAngularReadout_canonicalLogJetCoordinate
    hkappa omega m (homega m) s

/-- Especializacao das duas pontes a normalizacao de Haar `sqrt(2)`. -/
theorem finiteHaarTfvdAngularReadout_canonicalLogJetPort
    (M : ℕ) (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    finiteTfvdAngularReadout M tfvdHaarScale omega
        (canonicalLogJetTfvdCoordinate tfvdHaarScale omega · s) =
      finiteCanonicalAngularLogJetTrace M s :=
  finiteTfvdAngularReadout_canonicalLogJetPort
    M tfvdHaarScale_ne_zero omega homega s

end

end CPFormal.Analytic.Cp
