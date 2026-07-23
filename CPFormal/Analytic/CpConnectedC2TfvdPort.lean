import CPFormal.Analytic.CpConnectedC2Defect
import CPFormal.Analytic.CpSeededTfvdSameSBoundary

/-!
# Porta TFVD do cumulante conectado C2

O cumulante squarefree

`K_h = a_h(pq) - a_h(p) * a_h(q)`

ja possui uma realizacao exata na forma de bordo `same-s` existente:

`K_h = wedge(a_h(p), a_h(pq), 1, a_h(q))`.

Este modulo codifica essas quatro massas numa porta TFVD enriquecida. Depois
do retorno da valvula, a celula visivel e literalmente o cumulante C2 e a
celula dormente e zero. Aplicar Richardson nas duas portas formais `h=1/2`
e `h=1` recupera exatamente `(1/2) epsilonP epsilonQ`.

Esta e uma codificacao algebrica finita de coordenadas, sem Tate e sem
compressao escalar. Ela nao fornece ainda um intertwiner de operadores nem a
especializacao aritmetica que faria um zero Genuine fechar a porta: as
coordenadas canonicas atuais usam gradientes Dirichlet/log-Dirichlet, nao
massas C2 truncadas.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-! ## Massas deformadas e wedge conectado -/

/-- Massa real deformada `1 - h * epsilon`, vista no carrier complexo. -/
def c2DeformedMass (h epsilon : ℝ) : ℂ :=
  ((1 - h * epsilon : ℝ) : ℂ)

/-- O cumulante conectado e literalmente a celula de bordo `same-s`. -/
theorem c2PairConnectedCumulant_ofReal_eq_sameSEdgeBoundaryWedge
    (h epsilonP epsilonQ epsilonPQ : ℝ) :
    ((c2PairConnectedCumulant h epsilonP epsilonQ epsilonPQ : ℝ) : ℂ) =
      sameSEdgeBoundaryWedge
        (c2DeformedMass h epsilonP)
        (c2DeformedMass h epsilonPQ)
        1
        (c2DeformedMass h epsilonQ) := by
  unfold c2PairConnectedCumulant c2DeformedMass
    sameSEdgeBoundaryWedge
  push_cast
  ring

/-! ## Codificacao na porta TFVD enriquecida -/

/-- Porta de valor com as massas `a_h(p),a_h(pq)` nas duas arestas visiveis. -/
def c2MassTfvdValueCoordinate
    (block : ℕ) (kappa omega : ℂ)
    (h epsilonP epsilonPQ : ℝ) :
    EnrichedAngularTfvdCoordinate :=
  enrichedAngularTfvdEncode block kappa omega
    (c2DeformedMass h epsilonP)
    (c2DeformedMass h epsilonPQ)
    0

/-- Porta conjugada do cumulante: as arestas visiveis sao `1,a_h(q)`. -/
def c2MassTfvdJetCoordinate
    (block : ℕ) (kappa omega : ℂ)
    (h epsilonQ : ℝ) :
    EnrichedAngularTfvdCoordinate :=
  enrichedAngularTfvdEncode block kappa omega
    1
    (c2DeformedMass h epsilonQ)
    0

/-- Retornar as duas portas produz o cumulante na celula visivel e zero na
celula dormente. -/
theorem c2MassTfvdBoundaryCells_eq
    (block : ℕ) {kappa omega : ℂ}
    (hkappa : kappa ≠ 0) (homega : omega ≠ 0)
    (h epsilonP epsilonQ epsilonPQ : ℝ) :
    enrichedTfvdSameSBoundaryCells kappa omega
        (c2MassTfvdValueCoordinate
          block kappa omega h epsilonP epsilonPQ)
        (c2MassTfvdJetCoordinate
          block kappa omega h epsilonQ) =
      {
        visibleCell :=
          ((c2PairConnectedCumulant
            h epsilonP epsilonQ epsilonPQ : ℝ) : ℂ)
        dormantCell := 0
      } := by
  unfold c2MassTfvdValueCoordinate c2MassTfvdJetCoordinate
  rw [enrichedTfvdSameSBoundaryCells_encode block hkappa homega]
  apply TfvdSameSBoundaryCells.ext
  · exact
      (c2PairConnectedCumulant_ofReal_eq_sameSEdgeBoundaryWedge
        h epsilonP epsilonQ epsilonPQ).symm
  · unfold sameSEdgeBoundaryWedge
    ring

/-- Forma escalar da identificacao da celula visivel. -/
theorem c2MassTfvdBoundaryCells_visible_eq
    (block : ℕ) {kappa omega : ℂ}
    (hkappa : kappa ≠ 0) (homega : omega ≠ 0)
    (h epsilonP epsilonQ epsilonPQ : ℝ) :
    (enrichedTfvdSameSBoundaryCells kappa omega
        (c2MassTfvdValueCoordinate
          block kappa omega h epsilonP epsilonPQ)
        (c2MassTfvdJetCoordinate
          block kappa omega h epsilonQ)).visibleCell =
      ((c2PairConnectedCumulant
        h epsilonP epsilonQ epsilonPQ : ℝ) : ℂ) := by
  rw [c2MassTfvdBoundaryCells_eq
    block hkappa homega h epsilonP epsilonQ epsilonPQ]

/-- Como a celula dormente e zero, a sintese total preserva exatamente o
cumulante conectado, sem termo off-diagonal. -/
theorem c2MassTfvdBoundaryCells_total_eq
    (block : ℕ) {kappa omega : ℂ}
    (hkappa : kappa ≠ 0) (homega : omega ≠ 0)
    (h epsilonP epsilonQ epsilonPQ : ℝ) :
    (enrichedTfvdSameSBoundaryCells kappa omega
        (c2MassTfvdValueCoordinate
          block kappa omega h epsilonP epsilonPQ)
        (c2MassTfvdJetCoordinate
          block kappa omega h epsilonQ)).total =
      ((c2PairConnectedCumulant
        h epsilonP epsilonQ epsilonPQ : ℝ) : ℂ) := by
  rw [c2MassTfvdBoundaryCells_eq
    block hkappa homega h epsilonP epsilonQ epsilonPQ]
  simp [TfvdSameSBoundaryCells.total]

/-! ## Richardson dentro da porta -/

/-- A extrapolacao de Richardson das celulas TFVD e exatamente o produto
conectado das duas marginais. -/
theorem c2MassTfvdBoundaryCells_richardson_eq
    (block : ℕ) {kappa omega : ℂ}
    (hkappa : kappa ≠ 0) (homega : omega ≠ 0)
    (epsilonP epsilonQ epsilonPQ : ℝ) :
    2 *
        (enrichedTfvdSameSBoundaryCells kappa omega
          (c2MassTfvdValueCoordinate
            block kappa omega (1 / 2) epsilonP epsilonPQ)
          (c2MassTfvdJetCoordinate
            block kappa omega (1 / 2) epsilonQ)).visibleCell -
      (enrichedTfvdSameSBoundaryCells kappa omega
        (c2MassTfvdValueCoordinate
          block kappa omega 1 epsilonP epsilonPQ)
        (c2MassTfvdJetCoordinate
          block kappa omega 1 epsilonQ)).visibleCell =
      (((1 / 2) * epsilonP * epsilonQ : ℝ) : ℂ) := by
  rw [c2MassTfvdBoundaryCells_visible_eq
      block hkappa homega (1 / 2) epsilonP epsilonQ epsilonPQ,
    c2MassTfvdBoundaryCells_visible_eq
      block hkappa homega 1 epsilonP epsilonQ epsilonPQ]
  have hRichardson :=
    congrArg (fun x : ℝ => (x : ℂ))
      (c2PairRichardsonDefect_eq epsilonP epsilonQ epsilonPQ)
  simpa [c2PairRichardsonDefect] using hRichardson

/-- A mesma identidade depois da sintese das duas celulas; como a dormente e
zero, nenhuma informacao conectada e perdida. -/
theorem c2MassTfvdBoundaryCells_total_richardson_eq
    (block : ℕ) {kappa omega : ℂ}
    (hkappa : kappa ≠ 0) (homega : omega ≠ 0)
    (epsilonP epsilonQ epsilonPQ : ℝ) :
    2 *
        (enrichedTfvdSameSBoundaryCells kappa omega
          (c2MassTfvdValueCoordinate
            block kappa omega (1 / 2) epsilonP epsilonPQ)
          (c2MassTfvdJetCoordinate
            block kappa omega (1 / 2) epsilonQ)).total -
      (enrichedTfvdSameSBoundaryCells kappa omega
        (c2MassTfvdValueCoordinate
          block kappa omega 1 epsilonP epsilonPQ)
        (c2MassTfvdJetCoordinate
          block kappa omega 1 epsilonQ)).total =
      (((1 / 2) * epsilonP * epsilonQ : ℝ) : ℂ) := by
  rw [c2MassTfvdBoundaryCells_total_eq
      block hkappa homega (1 / 2) epsilonP epsilonQ epsilonPQ,
    c2MassTfvdBoundaryCells_total_eq
      block hkappa homega 1 epsilonP epsilonQ epsilonPQ]
  have hRichardson :=
    congrArg (fun x : ℝ => (x : ℂ))
      (c2PairRichardsonDefect_eq epsilonP epsilonQ epsilonPQ)
  simpa [c2PairRichardsonDefect] using hRichardson

end

end CPFormal.Analytic.Cp
