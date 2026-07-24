import CPFormal.Analytic.CpGenuineCrossPrimeObservability
import CPFormal.Analytic.CpGenuineKernelPrimeState
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Inclusao do kernel Genuine no kernel Green

Este modulo formaliza diretamente a estrategia

`genuineContinuation s = 0 -> canal Green s = 0`.

O objetivo e separar a formulacao estrutural da ponte de suas varias
realizacoes ja presentes no projeto. Para duas cameras primas distintas,
provamos que sao equivalentes:

* inclusao do kernel Genuine no kernel do vetor Green limite;
* concordancia das duas coordenadas Green;
* sincronizacao assintotica das proveniencias `same-s`;
* fechamento do gap de proveniencia numa reindexacao cofinal;
* anulacao do operador Genuine--Green completado em todo zero Genuine;
* existencia do estado multiprima do kernel;
* saturacao do carry;
* nao anulacao forte do Genuine fora da meia-abscissa.

Essas equivalencias sao um guarda de escopo. Em particular, a forma TFVD
comum elimina o bordo, mas a sincronizacao das proveniencias nao e uma
consequencia formal mais fraca: para cameras distintas ela ja contem
exatamente a localizacao critica.

Nenhuma das proposicoes globais abaixo e declarada como instancia.
-/

open scoped Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-! ## Formulacoes globais da inclusao de kernels -/

/-- Todo zero Genuine no strip pertence ao kernel do vetor Green limite. -/
def GenuineKernelIncludedInGreenLimitKernel (p q : ℕ) : Prop :=
  ∀ {s : ℂ}, genuineContinuation s = 0 →
    s ∈ genuineCriticalStrip →
      crossPrimeAlignedGreenLimitVector p q s = 0

/-- Forma aparentemente mais fraca: num zero Genuine, as duas cameras Green
limite fornecem a mesma coordenada. Para primos distintos ela sera equivalente
a anulacao do vetor inteiro. -/
def GenuineKernelSynchronizesGreenLimitCoordinates (p q : ℕ) : Prop :=
  ∀ {s : ℂ}, genuineContinuation s = 0 →
    s ∈ genuineCriticalStrip →
      crossPrimeAlignedGreenLimitVector p q s (0 : Fin 2) =
        crossPrimeAlignedGreenLimitVector p q s (1 : Fin 2)

/-- Forma TFVD da mesma tentativa: num zero Genuine, a diferenca real das
proveniencias `same-s` de duas cameras tende a zero. -/
def GenuineKernelSynchronizesTfvdProvenance (p q : ℕ) : Prop :=
  ∀ {s : ℂ}, genuineContinuation s = 0 →
    s ∈ genuineCriticalStrip →
      Tendsto
        (fun M : ℕ =>
          (finiteCanonicalTfvdSameSGreenProvenanceDefect p M s -
            finiteCanonicalTfvdSameSGreenProvenanceDefect q M s).re)
        atTop (nhds 0)

/-- Alvo operacional assintotico mais fraco que o fechamento da sequencia
inteira: basta uma reindexacao cofinal dos cutoffs ao longo da qual o gap real
de proveniencia tende a zero. A sequencia completa ja possui um limite radial
explicito, portanto uma unica reindexacao de fechamento determina esse limite.
Uma subsequencia estritamente crescente e um caso particular. -/
def GenuineKernelHasTfvdProvenanceZeroCofinalReindex (p q : ℕ) : Prop :=
  ∀ {s : ℂ}, genuineContinuation s = 0 →
    s ∈ genuineCriticalStrip →
      ∃ φ : ℕ → ℕ,
        Tendsto φ atTop atTop ∧
          Tendsto
            (fun N : ℕ =>
              (finiteCanonicalTfvdSameSGreenProvenanceDefect p (φ N) s -
                finiteCanonicalTfvdSameSGreenProvenanceDefect q (φ N) s).re)
            atTop (nhds 0)

/-- Forma pelo operador completado: todo zero do bloco Genuine fecha tambem
o bloco Green, logo fecha a soma direta. -/
def GenuineKernelClosesCompletedLimitOperator (p q : ℕ) : Prop :=
  ∀ {s : ℂ}, genuineContinuation s = 0 →
    s ∈ genuineCriticalStrip →
      genuineGreenCompletedLimitOperator p q s = 0

/-- Enunciado escalar forte no strip, isolado para comparar com a inclusao de
kernels sem esconder a contrapositiva. -/
def GenuineStrongNonvanishingInStrip : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
    s.re ≠ (1 : ℝ) / 2 →
      genuineContinuation s ≠ 0

/-! ## Concordancia de duas cameras -/

/-- Para duas cameras primas distintas, concordar no limite e equivalente a
anular o vetor Green inteiro em cada zero Genuine. -/
theorem genuineKernelIncludedInGreenLimitKernel_iff_coordinates
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    GenuineKernelIncludedInGreenLimitKernel p q ↔
      GenuineKernelSynchronizesGreenLimitCoordinates p q := by
  constructor
  · intro hinclusion s hzero hs
    have hvector := hinclusion hzero hs
    simp [hvector]
  · intro hagreement s hzero hs
    have hcritical :
        criticalDisplacement s.re = 0 :=
      (crossPrimeAlignedGreenLimitVector_coordinates_eq_iff
        p q hp hq hpq hs).1 (hagreement hzero hs)
    exact
      (crossPrimeAlignedGreenLimitVector_eq_zero_iff_criticalDisplacement_eq_zero
        p q hp hq hs).2 hcritical

/-- A sincronizacao assintotica das proveniencias `same-s` e a mesma inclusao
de kernels. A identidade de bordo comum nao fornece essa sincronizacao de
graca; ela apenas troca a diferenca de proveniencias pela diferenca Green. -/
theorem genuineKernelIncludedInGreenLimitKernel_iff_tfvdProvenance
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    GenuineKernelIncludedInGreenLimitKernel p q ↔
      GenuineKernelSynchronizesTfvdProvenance p q := by
  constructor
  · intro hinclusion s hzero hs
    have hcritical :
        criticalDisplacement s.re = 0 :=
      (crossPrimeAlignedGreenLimitVector_eq_zero_iff_criticalDisplacement_eq_zero
        p q hp hq hs).1 (hinclusion hzero hs)
    exact
      (finiteCanonicalTfvdSameSGreenProvenanceDefect_re_sub_tendsto_zero_iff
        p q hp hq hpq hs).2 hcritical
  · intro hprovenance s hzero hs
    have hcritical :
        criticalDisplacement s.re = 0 :=
      (finiteCanonicalTfvdSameSGreenProvenanceDefect_re_sub_tendsto_zero_iff
        p q hp hq hpq hs).1 (hprovenance hzero hs)
    exact
      (crossPrimeAlignedGreenLimitVector_eq_zero_iff_criticalDisplacement_eq_zero
        p q hp hq hs).2 hcritical

/-- Nem o fechamento da sequencia inteira e necessario: uma reindexacao
cofinal com gap de proveniencia tendendo a zero ja forca o kernel Green. -/
theorem genuineKernelIncludedInGreenLimitKernel_iff_tfvdProvenanceZeroCofinalReindex
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    GenuineKernelIncludedInGreenLimitKernel p q ↔
      GenuineKernelHasTfvdProvenanceZeroCofinalReindex p q := by
  constructor
  · intro hinclusion s hzero hs
    have hcritical :
        criticalDisplacement s.re = 0 :=
      (crossPrimeAlignedGreenLimitVector_eq_zero_iff_criticalDisplacement_eq_zero
        p q hp hq hs).1 (hinclusion hzero hs)
    refine ⟨id, tendsto_id, ?_⟩
    simpa using
      (finiteCanonicalTfvdSameSGreenProvenanceDefect_re_sub_tendsto_zero_iff
        p q hp hq hpq hs).2 hcritical
  · intro hreindex s hzero hs
    rcases hreindex hzero hs with ⟨φ, hφ, hzeroReindex⟩
    let delta := criticalDisplacement s.re
    let E := infiniteReflectedGreenEnergy s
    have hlimit :=
      finiteCanonicalTfvdSameSGreenProvenanceDefect_re_sub_tendsto
        p q hp hq hs
    have hlimitReindex := hlimit.comp hφ
    have hproduct :
        (cpRadialDifference q delta - cpRadialDifference p delta) * E = 0 := by
      simpa [delta, E, Function.comp_def] using
        tendsto_nhds_unique hlimitReindex hzeroReindex
    have hE : E ≠ 0 :=
      ne_of_gt (infiniteReflectedGreenEnergy_pos hs)
    have hcoefficient :
        cpRadialDifference q delta - cpRadialDifference p delta = 0 :=
      (mul_eq_zero.mp hproduct).resolve_right hE
    have heq :
        cpRadialDifference p delta = cpRadialDifference q delta := by
      linarith
    have hcritical :
        criticalDisplacement s.re = 0 := by
      simpa [delta] using
        (cpRadialDifference_eq_cpRadialDifference_iff
          p q hp hq hpq delta).1 heq
    exact
      (crossPrimeAlignedGreenLimitVector_eq_zero_iff_criticalDisplacement_eq_zero
        p q hp hq hs).2 hcritical

/-! ## Operador completado, estado multiprima e carry -/

/-- Fechar o operador completado em cada zero Genuine e exatamente incluir o
kernel Genuine no kernel Green. -/
theorem genuineKernelIncludedInGreenLimitKernel_iff_completedOperator
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    GenuineKernelIncludedInGreenLimitKernel p q ↔
      GenuineKernelClosesCompletedLimitOperator p q := by
  constructor
  · intro hinclusion s hzero hs
    have hcritical :
        criticalDisplacement s.re = 0 :=
      (crossPrimeAlignedGreenLimitVector_eq_zero_iff_criticalDisplacement_eq_zero
        p q hp hq hs).1 (hinclusion hzero hs)
    exact
      (genuineGreenCompletedLimitOperator_eq_zero_iff
        p q hp hq hs).2 ⟨hzero, hcritical⟩
  · intro hcompleted s hzero hs
    have hcritical :
        criticalDisplacement s.re = 0 :=
      ((genuineGreenCompletedLimitOperator_eq_zero_iff
        p q hp hq hs).1 (hcompleted hzero hs)).2
    exact
      (crossPrimeAlignedGreenLimitVector_eq_zero_iff_criticalDisplacement_eq_zero
        p q hp hq hs).2 hcritical

/-- A inclusao no kernel Green e equivalente a construir o estado multiprima
do kernel. Assim, a formulacao vetorial nao e uma hipotese mais fraca que a
inclusao de kernels. -/
theorem genuineKernelIncludedInGreenLimitKernel_iff_primeGreenState
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    GenuineKernelIncludedInGreenLimitKernel p q ↔
      GenuineKernelHasPrimeGreenState := by
  constructor
  · intro hinclusion s hzero hs
    have hcritical :
        criticalDisplacement s.re = 0 :=
      (crossPrimeAlignedGreenLimitVector_eq_zero_iff_criticalDisplacement_eq_zero
        p q hp hq hs).1 (hinclusion hzero hs)
    exact
      (exists_isPrimeGreenBulkStateAt_iff_criticalDisplacement_eq_zero
        1 (by norm_num) hs).2 hcritical
  · intro hstate s hzero hs
    have hcritical :
        criticalDisplacement s.re = 0 :=
      (genuineKernelHasPrimeGreenState_iff.1 hstate) hzero hs
    exact
      (crossPrimeAlignedGreenLimitVector_eq_zero_iff_criticalDisplacement_eq_zero
        p q hp hq hs).2 hcritical

/-- A inclusao de kernels e a saturacao do ramo em qualquer camera prima. -/
theorem genuineKernelIncludedInGreenLimitKernel_iff_saturatesCarry
    (p q r : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hr : Nat.Prime r) :
    GenuineKernelIncludedInGreenLimitKernel p q ↔
      GenuineZeroSaturatesCarry r := by
  constructor
  · intro hinclusion s hzero hs
    have hcritical :
        criticalDisplacement s.re = 0 :=
      (crossPrimeAlignedGreenLimitVector_eq_zero_iff_criticalDisplacement_eq_zero
        p q hp hq hs).1 (hinclusion hzero hs)
    apply (branchNormSq_eq_one_iff r hr hs.1).2
    unfold criticalDisplacement at hcritical
    linarith
  · intro hsaturates s hzero hs
    have hre : s.re = (1 : ℝ) / 2 :=
      (branchNormSq_eq_one_iff r hr hs.1).1
        (hsaturates hzero hs)
    apply
      (crossPrimeAlignedGreenLimitVector_eq_zero_iff_criticalDisplacement_eq_zero
        p q hp hq hs).2
    unfold criticalDisplacement
    linarith

/-! ## Equivalencia com o `ne 0` forte -/

/-- A estrategia `kernel Genuine subset kernel Green` e logicamente
equivalente ao `ne 0` forte no strip. A equivalencia nao invalida a estrategia,
mas impede que a inclusao seja usada como se ja fosse um lema mais fraco. -/
theorem genuineKernelIncludedInGreenLimitKernel_iff_strongNonvanishing
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    GenuineKernelIncludedInGreenLimitKernel p q ↔
      GenuineStrongNonvanishingInStrip := by
  constructor
  · intro hinclusion s hs hoff hzero
    have hcritical :
        criticalDisplacement s.re = 0 :=
      (crossPrimeAlignedGreenLimitVector_eq_zero_iff_criticalDisplacement_eq_zero
        p q hp hq hs).1 (hinclusion hzero hs)
    apply hoff
    unfold criticalDisplacement at hcritical
    linarith
  · intro hstrong s hzero hs
    apply
      (crossPrimeAlignedGreenLimitVector_eq_zero_iff_criticalDisplacement_eq_zero
        p q hp hq hs).2
    by_contra hcritical
    have hoff : s.re ≠ (1 : ℝ) / 2 := by
      intro hre
      apply hcritical
      unfold criticalDisplacement
      linarith
    exact (hstrong hs hoff) hzero

/-- Para duas cameras distintas, a versao de concordancia proposta e tambem
exatamente o enunciado escalar forte. -/
theorem genuineKernelSynchronizesGreenLimitCoordinates_iff_strongNonvanishing
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    GenuineKernelSynchronizesGreenLimitCoordinates p q ↔
      GenuineStrongNonvanishingInStrip := by
  rw [← genuineKernelIncludedInGreenLimitKernel_iff_coordinates
      p q hp hq hpq,
    genuineKernelIncludedInGreenLimitKernel_iff_strongNonvanishing
      p q hp hq]

/-- O mesmo guarda de escopo na linguagem TFVD de proveniencia. -/
theorem genuineKernelSynchronizesTfvdProvenance_iff_strongNonvanishing
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    GenuineKernelSynchronizesTfvdProvenance p q ↔
      GenuineStrongNonvanishingInStrip := by
  rw [← genuineKernelIncludedInGreenLimitKernel_iff_tfvdProvenance
      p q hp hq hpq,
    genuineKernelIncludedInGreenLimitKernel_iff_strongNonvanishing
      p q hp hq]

/-- Mesmo uma unica reindexacao cofinal de fechamento do gap TFVD, em cada
zero Genuine, ja e equivalente ao enunciado forte. -/
theorem genuineKernelHasTfvdProvenanceZeroCofinalReindex_iff_strongNonvanishing
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    GenuineKernelHasTfvdProvenanceZeroCofinalReindex p q ↔
      GenuineStrongNonvanishingInStrip := by
  rw [←
      genuineKernelIncludedInGreenLimitKernel_iff_tfvdProvenanceZeroCofinalReindex
        p q hp hq hpq,
    genuineKernelIncludedInGreenLimitKernel_iff_strongNonvanishing
      p q hp hq]

end

end CPFormal.Analytic.Cp
