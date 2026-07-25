import CPFormal.Analytic.CpGenuineFirstMultibaseCutoff
import CPFormal.Analytic.CpGenuineGreenKernelInclusion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Defeito conectado C2 e guarda de Richardson

Este modulo formaliza o nucleo exato da antiga teoria dos defeitos C2 que e
relevante para o gargalo Genuine--Green.

Para massas deformadas

`a_h(p) = 1 - h * epsilon_p`,

o cumulante de um par e

`K_h = a_h(pq) - a_h(p) * a_h(q)`.

A extrapolacao de Richardson `2 K_(1/2) - K_1` cancela inclusive o defeito
conjunto desconhecido `epsilon_pq` e deixa exatamente

`(1 / 2) * epsilon_p * epsilon_q`.

Tambem registramos um guarda decisivo. O defeito cross-prime ja existente no
projeto e independente do parametro de escala alinhada. A combinacao formal
associada a reindexacao `L -> 2L` devolve o proprio defeito, portanto nao
fabrica o cumulante conectado. Como o cutoff alinhado possui ainda um termo
afim, essa reindexacao nem deve ser confundida sem prova com `M -> 2M`.

Os simbolos `p` e `q` tem papeis diferentes nas duas construcoes originais:
na teoria C2 sao fatores vistos por um mesmo cutoff; no projeto Cp sao cameras
distintas. A especializacao radial abaixo e apenas um detector-modelo positivo,
nao uma identificacao entre `epsilon_M` e `cpRadialDifference`.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-! ## Cumulante conectado abstrato -/

/-- Cumulante conectado de duas massas deformadas pela escala `h`. -/
def c2PairConnectedCumulant
    (h epsilonP epsilonQ epsilonPQ : ℝ) : ℝ :=
  (1 - h * epsilonPQ) -
    (1 - h * epsilonP) * (1 - h * epsilonQ)

/-- Defeito de Richardson entre as escalas formais `h = 1` e `h = 1/2`. -/
def c2PairRichardsonDefect
    (epsilonP epsilonQ epsilonPQ : ℝ) : ℝ :=
  2 * c2PairConnectedCumulant (1 / 2) epsilonP epsilonQ epsilonPQ -
    c2PairConnectedCumulant 1 epsilonP epsilonQ epsilonPQ

/-- Richardson cancela todos os termos lineares e o defeito conjunto
`epsilonPQ`, isolando o produto conectado das duas marginais. -/
theorem c2PairRichardsonDefect_eq
    (epsilonP epsilonQ epsilonPQ : ℝ) :
    c2PairRichardsonDefect epsilonP epsilonQ epsilonPQ =
      (1 / 2) * epsilonP * epsilonQ := by
  unfold c2PairRichardsonDefect c2PairConnectedCumulant
  ring

/-- Em particular, dentro do modelo comum `a_h = 1 - h * epsilon` para todo
o suporte — isto e, incluindo o halving do termo conjunto — o resultado nao
depende do valor de `epsilonPQ`. -/
theorem c2PairRichardsonDefect_independent_of_joint
    (epsilonP epsilonQ epsilonPQ epsilonPQ' : ℝ) :
    c2PairRichardsonDefect epsilonP epsilonQ epsilonPQ =
      c2PairRichardsonDefect epsilonP epsilonQ epsilonPQ' := by
  rw [c2PairRichardsonDefect_eq, c2PairRichardsonDefect_eq]

/-- O defeito conectado e positivo quando as duas marginais sao positivas. -/
theorem c2PairRichardsonDefect_pos
    {epsilonP epsilonQ epsilonPQ : ℝ}
    (hP : 0 < epsilonP) (hQ : 0 < epsilonQ) :
    0 < c2PairRichardsonDefect epsilonP epsilonQ epsilonPQ := by
  rw [c2PairRichardsonDefect_eq]
  positivity

/-! ## Detector radial-modelo -/

/-- Analogo radial do produto conectado C2 para duas cameras. Esta definicao
nao identifica os defeitos de massa C2 com os desequilibrios radiais. -/
def crossPrimeRadialC2Detector
    (p q : ℕ) (delta : ℝ) : ℝ :=
  (1 / 2) * cpRadialDifference p delta *
    cpRadialDifference q delta

/-- O detector radial pode ser escrito como um Richardson conectado com
qualquer termo conjunto, pois esse termo e cancelado. -/
theorem crossPrimeRadialC2Detector_eq_richardson
    (p q : ℕ) (delta epsilonPQ : ℝ) :
    crossPrimeRadialC2Detector p q delta =
      c2PairRichardsonDefect
        (cpRadialDifference p delta)
        (cpRadialDifference q delta)
        epsilonPQ := by
  rw [c2PairRichardsonDefect_eq]
  rfl

/-- Fatoracao do detector em `delta^2` e dois cofatores positivos. -/
theorem crossPrimeRadialC2Detector_eq_delta_sq_factor
    (p q : ℕ) (delta : ℝ) :
    crossPrimeRadialC2Detector p q delta =
      2 * delta ^ 2 *
        cpRadialCofactor p delta * cpRadialCofactor q delta := by
  rw [crossPrimeRadialC2Detector,
    cpRadialDifference_eq_two_mul_delta_mul_cofactor,
    cpRadialDifference_eq_two_mul_delta_mul_cofactor]
  ring

/-- Para duas bases primas, o detector-modelo e estritamente positivo fora
do equilibrio critico. -/
theorem crossPrimeRadialC2Detector_pos
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    {delta : ℝ} (hdelta : delta ≠ 0) :
    0 < crossPrimeRadialC2Detector p q delta := by
  rw [crossPrimeRadialC2Detector_eq_delta_sq_factor]
  have hdeltaSq : 0 < delta ^ 2 := sq_pos_of_ne_zero hdelta
  have hpCofactor : 0 < cpRadialCofactor p delta :=
    cpRadialCofactor_pos p hp delta
  have hqCofactor : 0 < cpRadialCofactor q delta :=
    cpRadialCofactor_pos q hq delta
  positivity

/-- Assim, o locus nulo do detector-modelo e exatamente `delta = 0`. -/
theorem crossPrimeRadialC2Detector_eq_zero_iff
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (delta : ℝ) :
    crossPrimeRadialC2Detector p q delta = 0 ↔ delta = 0 := by
  constructor
  · intro hzero
    by_contra hdelta
    exact (ne_of_gt
      (crossPrimeRadialC2Detector_pos p q hp hq hdelta)) hzero
  · rintro rfl
    simp [crossPrimeRadialC2Detector, cpRadialDifference]

/-! ## O defeito Genuine atual nao ganha conectividade por Richardson -/

/-- Como o defeito alinhado atual e independente de `L`, a combinacao formal
nas escalas `L` e `2L` e literalmente o mesmo detector rank-one. -/
theorem crossPrimeAlignedCutoffDefect_richardson_eq_self
    (p q L : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    2 * crossPrimeAlignedCutoffDefect p q (2 * L) s -
        crossPrimeAlignedCutoffDefect p q L s =
      crossPrimeAlignedCutoffDefect p q L s := by
  rw [crossPrimeAlignedCutoffDefect_eq_factor_sub_mul_genuine
      p q (2 * L) hp hpodd hq hqodd hs,
    crossPrimeAlignedCutoffDefect_eq_factor_sub_mul_genuine
      p q L hp hpodd hq hqodd hs]
  ring

/-- Consequentemente, num zero Genuine essa combinacao ingenua fecha, mas
apenas porque o defeito original ja fecha; ela nao produz o detector radial
acima. -/
theorem crossPrimeAlignedCutoffDefect_richardson_eq_zero_of_genuine_zero
    (p q L : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    2 * crossPrimeAlignedCutoffDefect p q (2 * L) s -
        crossPrimeAlignedCutoffDefect p q L s = 0 := by
  rw [crossPrimeAlignedCutoffDefect_richardson_eq_self
      p q L hp hpodd hq hqodd hs,
    crossPrimeAlignedCutoffDefect_eq_factor_sub_mul_genuine
      p q L hp hpodd hq hqodd hs,
    hzero, mul_zero]

/-! ## Guarda da ponte ainda ausente -/

/-- Intertwiner coercivo que uma rota C2--Gpre ainda precisaria construir:
todo zero Genuine no strip fecharia o detector conectado radial. -/
def GenuineKernelClosesRadialC2Detector (p q : ℕ) : Prop :=
  ∀ {s : ℂ}, genuineContinuation s = 0 →
    s ∈ genuineCriticalStrip →
      crossPrimeRadialC2Detector p q
        (criticalDisplacement s.re) = 0

/-- Fechar esse detector em todo zero Genuine e equivalente ao enunciado
forte. O teorema e um guarda contra usar o intertwiner ausente como se ja
fosse consequencia da algebra de cumulantes. -/
theorem genuineKernelClosesRadialC2Detector_iff_strongNonvanishing
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    GenuineKernelClosesRadialC2Detector p q ↔
      GenuineStrongNonvanishingInStrip := by
  constructor
  · intro hbridge s hs hoff hzero
    have hdelta :
        criticalDisplacement s.re = 0 :=
      (crossPrimeRadialC2Detector_eq_zero_iff
        p q hp hq (criticalDisplacement s.re)).1
        (hbridge hzero hs)
    exact hoff (by
      unfold criticalDisplacement at hdelta
      linarith)
  · intro hstrong s hzero hs
    apply
      (crossPrimeRadialC2Detector_eq_zero_iff
        p q hp hq (criticalDisplacement s.re)).2
    unfold criticalDisplacement
    by_contra hdelta
    have hre : s.re ≠ (1 : ℝ) / 2 := by
      intro hre
      apply hdelta
      linarith
    exact (hstrong hs hre) hzero

end

end CPFormal.Analytic.Cp
