import CPFormal.Analytic.CpFiniteGenuineTfvdProvenanceGluing
import CPFormal.Analytic.CpFiniteTfvdLogJetCriticalPhaseFan
import CPFormal.Analytic.CpGenuineSecondDifferenceIdentity

/-!
# Transporte exato entre o zero Genuine e o locus de saturacao do carry

Este modulo registra, sem esconder hipoteses, que os detectores construidos
ao longo da teoria possuem exatamente o mesmo locus:

* saturacao quadratica do ramo, `branchNormSq p sigma = 1`;
* anulacao do defeito do ramo;
* anulacao do tilt transversal em qualquer centro admissivel;
* fechamento do fluxo Green bracketado;
* fechamento do ledger enriquecido TFVD--log-jet--Green--bordo.

Num zero do `genuineContinuation`, todas essas condicoes sao equivalentes a
`re(s) = 1 / 2`. Isso permite formular a obrigacao final numa unica interface
e transporta qualquer prova futura entre as linguagens sem refazer a
geometria de carry.

Importante: o modulo nao declara uma instancia da obrigacao final. Provar que
todo zero Genuine satisfaz qualquer uma das condicoes abaixo continua sendo
exatamente a seta aritmetica ainda ausente; assumir o fechamento do fluxo ou
do ledger seria equivalente a assumir a saturacao.
-/

open scoped Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-!
## Ledger nomeado
-/

/--
O valor real do ledger enriquecido no cutoff `M`. O defeito log-jet--Green e
mantido explicitamente, e o bordo bracketado usa o cutoff alinhado `3 * M`.
-/
def finiteCanonicalEnrichedGenuineCarryLedger
    (p M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) : ℝ :=
  (finiteCanonicalEnrichedTfvdReflectedLogJetWedgeTrace
      M kappa omega s -
    finiteCanonicalLogJetGreenDefectTrace p M s +
    finiteCanonicalAngularBracketCoupledBoundary M s).re

/-- Proposicao pontual de fechamento do ledger enriquecido. -/
def EnrichedGenuineCarryLedgerClosesAt
    (p : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) : Prop :=
  Tendsto
    (fun M : ℕ ↦
      finiteCanonicalEnrichedGenuineCarryLedger p M kappa omega s)
    atTop (nhds 0)

/-- Num zero Genuine, fechar o ledger nomeado equivale a estar na meia reta. -/
theorem enrichedGenuineCarryLedgerClosesAt_iff_re_eq_half_of_genuine_zero
    (p : ℕ) (hp : Nat.Prime p)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    EnrichedGenuineCarryLedgerClosesAt p kappa omega s ↔
      s.re = (1 : ℝ) / 2 := by
  simpa [EnrichedGenuineCarryLedgerClosesAt,
    finiteCanonicalEnrichedGenuineCarryLedger] using
    (enrichedLedger_tendsto_zero_iff_re_eq_half_of_genuine_zero
      p hp hkappa omega homega hs hzero)

/-!
## Transporte pontual para os detectores de carry
-/

/--
No zero Genuine, a saturacao original do ramo e exatamente o fechamento da
colagem enriquecida. Esta e a forma direta do transporte pedido; nenhuma das
duas condicoes e descartada ou inserida como fato auxiliar.
-/
theorem branchNormSq_eq_one_iff_enrichedGenuineCarryLedgerClosesAt_of_genuine_zero
    (p : ℕ) (hp : Nat.Prime p)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    branchNormSq p s.re = 1 ↔
      EnrichedGenuineCarryLedgerClosesAt p kappa omega s := by
  rw [branchNormSq_eq_one_iff p hp hs.1]
  exact
    (enrichedGenuineCarryLedgerClosesAt_iff_re_eq_half_of_genuine_zero
      p hp hkappa omega homega hs hzero).symm

/-- A mesma equivalencia escrita com o defeito quadratico do ramo. -/
theorem branchDefect_eq_zero_iff_enrichedGenuineCarryLedgerClosesAt_of_genuine_zero
    (p : ℕ) (hp : Nat.Prime p)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    branchDefect p s.re = 0 ↔
      EnrichedGenuineCarryLedgerClosesAt p kappa omega s := by
  rw [branchDefect, sub_eq_zero]
  exact
    branchNormSq_eq_one_iff_enrichedGenuineCarryLedgerClosesAt_of_genuine_zero
      p hp hkappa omega homega hs hzero

/--
Em qualquer centro admissivel, o zero do tilt e o fechamento do mesmo ledger
tambem sao a mesma obrigacao.
-/
theorem cpTiltAtSigma_eq_zero_iff_enrichedGenuineCarryLedgerClosesAt_of_genuine_zero
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {center : ℝ}
    (hcenter : (CPFormal.Genuine.Cp.halfRange p : ℝ) < center)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    cpTiltAtSigma p s.re center = 0 ↔
      EnrichedGenuineCarryLedgerClosesAt p kappa omega s := by
  exact
    (cpTiltAtSigma_eq_zero_iff_half
      p hp hpodd hs.1 hcenter).trans
        (enrichedGenuineCarryLedgerClosesAt_iff_re_eq_half_of_genuine_zero
          p hp hkappa omega homega hs hzero).symm

/-!
## Obrigacao global minima
-/

/--
Enunciado global, restrito ao dominio onde o Genuine canonico e as cartas
estao relacionados: todo zero Genuine no strip satura o ramo `C_p`.
-/
def GenuineZeroSaturatesCarry (p : ℕ) : Prop :=
  ∀ {s : ℂ}, genuineContinuation s = 0 →
    s ∈ genuineCriticalStrip → branchNormSq p s.re = 1

/-- Forma global equivalente usando a colagem enriquecida concreta. -/
def GenuineZerosCloseEnrichedCarryLedger
    (p : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) : Prop :=
  ∀ {s : ℂ}, genuineContinuation s = 0 →
    s ∈ genuineCriticalStrip →
      EnrichedGenuineCarryLedgerClosesAt p kappa omega s

/--
A obrigacao global de saturacao e equivalente, ponto a ponto, ao fechamento
do ledger enriquecido em todos os zeros. Assim a colagem muda a linguagem da
ponte, mas nao acrescenta a conclusao como hipotese oculta.
-/
theorem genuineZeroSaturatesCarry_iff_genuineZerosCloseEnrichedCarryLedger
    (p : ℕ) (hp : Nat.Prime p)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) :
    GenuineZeroSaturatesCarry p ↔
      GenuineZerosCloseEnrichedCarryLedger p kappa omega := by
  constructor
  · intro hsaturates s hzero hs
    exact
      (branchNormSq_eq_one_iff_enrichedGenuineCarryLedgerClosesAt_of_genuine_zero
        p hp hkappa omega homega hs hzero).mp
          (hsaturates hzero hs)
  · intro hcloses s hzero hs
    exact
      (branchNormSq_eq_one_iff_enrichedGenuineCarryLedgerClosesAt_of_genuine_zero
        p hp hkappa omega homega hs hzero).mpr
          (hcloses hzero hs)

/-- A versao antiga em termos de fluxo Green e a mesma obrigacao global. -/
theorem genuineZeroSaturatesCarry_iff_genuineCarryFluxBridge
    (p : ℕ) (hp : Nat.Prime p) :
    GenuineZeroSaturatesCarry p ↔ GenuineCarryFluxBridge p := by
  constructor
  · intro hsaturates
    refine ⟨?_⟩
    intro s hzero hs
    have hnorm : branchNormSq p s.re = 1 := hsaturates hzero hs
    have hdefect : branchDefect p s.re = 0 := by
      exact sub_eq_zero.mpr hnorm
    exact
      (branchDefect_eq_zero_iff_coupledFlux_tendsto_zero_of_genuine_zero
        p hp hs hzero).mp hdefect
  · intro hbridge s hzero hs
    have hdefect : branchDefect p s.re = 0 :=
      (branchDefect_eq_zero_iff_coupledFlux_tendsto_zero_of_genuine_zero
        p hp hs hzero).mpr
          (hbridge.flux_closes_at_zero hzero hs)
    exact sub_eq_zero.mp hdefect

/--
A obrigacao nao depende da camera prima escolhida: todas as normas de ramo
saturam exatamente na mesma meia abscissa.
-/
theorem genuineZeroSaturatesCarry_prime_independent
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    GenuineZeroSaturatesCarry p ↔ GenuineZeroSaturatesCarry q := by
  constructor
  · intro hpSaturates s hzero hs
    have hre : s.re = (1 : ℝ) / 2 :=
      (branchNormSq_eq_one_iff p hp hs.1).mp
        (hpSaturates hzero hs)
    exact (branchNormSq_eq_one_iff q hq hs.1).mpr hre
  · intro hqSaturates s hzero hs
    have hre : s.re = (1 : ℝ) / 2 :=
      (branchNormSq_eq_one_iff q hq hs.1).mp
        (hqSaturates hzero hs)
    exact (branchNormSq_eq_one_iff p hp hs.1).mpr hre

/-- Uma prova da obrigacao minima entrega a localizacao dos zeros no strip. -/
theorem re_eq_half_of_genuine_zero_of_saturatesCarry
    (p : ℕ) (hp : Nat.Prime p)
    (htransport : GenuineZeroSaturatesCarry p)
    {s : ℂ} (hzero : genuineContinuation s = 0)
    (hs : s ∈ genuineCriticalStrip) :
    s.re = (1 : ℝ) / 2 :=
  (branchNormSq_eq_one_iff p hp hs.1).mp
    (htransport hzero hs)

end

end CPFormal.Analytic.Cp
