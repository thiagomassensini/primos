import CPFormal.Analytic.CpGenuineFirstOrthogonalGreenLimit
import CPFormal.Analytic.CpGenuineCarrySaturationTransport
import CPFormal.Analytic.CpFiniteSeededTfvdGreenIdentity
import CPFormal.Analytic.CpCarryWeightedVerticalBoundaryPencil

/-!
# Gate final Genuine-first entre os dois operadores limite

Este modulo coloca a ultima colagem numa proposicao de kernel, sem inserir a
seta procurada como campo de uma estrutura.

O operador Genuine ortogonal e o limite das cameras bracketadas. O vetor
Green ortogonal e o limite exato dos fluxos depois que o bordo de cutoff
fecha. A obrigacao final e, portanto, a inclusao

```
ker GenuineLimitOperator ⊆ ker GreenLimitVector.
```

O arquivo prova que essa inclusao e equivalente, sem perda de informacao, a:

* todo zero Genuine no strip estar na meia-abscissa;
* todo zero Genuine saturar o carry;
* todo zero Genuine fechar o observavel radial TFVD--Green semeado.

A identidade livre de retorno tambem e registrada pelo seu alcance exato:
antes da colagem aritmetica, todo valor complexo e caracteristico. Assim o
retorno esta completo, mas nao seleciona sozinho o kernel aritmetico.
Nenhuma das proposicoes equivalentes abaixo e declarada como teorema
incondicional, instancia, axioma ou hipotese escondida.
-/

open scoped Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-! ## A inclusao nua dos nucleos -/

/-- A ultima seta Genuine-first, escrita diretamente entre os dois objetos
limite e restrita ao strip onde suas identificacoes canonicas valem. -/
def OrthogonalGenuineKernelIncludedInGreenKernel
    (p q : ℕ) : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
    orthogonalGenuineLimitOperator s = 0 →
      crossPrimeAlignedGreenLimitVector p q s = 0

/-- A mesma obrigacao escrita sem operadores auxiliares. -/
def GenuineZerosLieOnCriticalLine : Prop :=
  ∀ {s : ℂ}, genuineContinuation s = 0 →
    s ∈ genuineCriticalStrip →
      s.re = (1 : ℝ) / 2

/-- Fechamento global do observavel radial concreto construido pela porta
TFVD semeada, pelo Green e pela proveniencia preservada. -/
def GenuineZerosCloseSeededTfvdGreenRadialObservable
    (p : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) : Prop :=
  ∀ {s : ℂ}, genuineContinuation s = 0 →
    s ∈ genuineCriticalStrip →
      SeededTfvdGreenRadialClosureAt p kappa omega s

/-- A inclusao dos nucleos limite e literalmente a localizacao dos zeros
Genuine na meia-abscissa. -/
theorem orthogonalGenuineKernelIncludedInGreenKernel_iff_genuineZerosLieOnCriticalLine
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    OrthogonalGenuineKernelIncludedInGreenKernel p q ↔
      GenuineZerosLieOnCriticalLine := by
  constructor
  · intro hinclude s hzero hs
    have hop : orthogonalGenuineLimitOperator s = 0 :=
      (orthogonalGenuineLimitOperator_eq_zero_iff s).2 hzero
    have hgreen :
        crossPrimeAlignedGreenLimitVector p q s = 0 :=
      hinclude hs hop
    have hcritical : criticalDisplacement s.re = 0 :=
      (crossPrimeAlignedGreenLimitVector_eq_zero_iff_criticalDisplacement_eq_zero
        p q hp hq hs).1 hgreen
    unfold criticalDisplacement at hcritical
    linarith
  · intro hcritical s hs hop
    have hzero : genuineContinuation s = 0 :=
      (orthogonalGenuineLimitOperator_eq_zero_iff s).1 hop
    have hre : s.re = (1 : ℝ) / 2 := hcritical hzero hs
    apply
      (crossPrimeAlignedGreenLimitVector_eq_zero_iff_criticalDisplacement_eq_zero
        p q hp hq hs).2
    unfold criticalDisplacement
    linarith

/-- A linguagem de carry nao enfraquece nem fortalece o gate final: a
saturacao global e a mesma inclusao de kernels. -/
theorem orthogonalGenuineKernelIncludedInGreenKernel_iff_genuineZeroSaturatesCarry
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    OrthogonalGenuineKernelIncludedInGreenKernel p q ↔
      GenuineZeroSaturatesCarry p := by
  rw [orthogonalGenuineKernelIncludedInGreenKernel_iff_genuineZerosLieOnCriticalLine
    p q hp hq]
  constructor
  · intro hcritical s hzero hs
    exact (branchNormSq_eq_one_iff p hp hs.1).2
      (hcritical hzero hs)
  · intro hsaturates s hzero hs
    exact (branchNormSq_eq_one_iff p hp hs.1).1
      (hsaturates hzero hs)

/-- A colagem concreta TFVD--Green semeada tambem e exatamente o gate final.
O endpoint Genuine ja fecha; o que resta e o observavel radial, sem descartar
o defeito de proveniencia. -/
theorem orthogonalGenuineKernelIncludedInGreenKernel_iff_seededTfvdRadialClosure
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) :
    OrthogonalGenuineKernelIncludedInGreenKernel p q ↔
      GenuineZerosCloseSeededTfvdGreenRadialObservable
        p kappa omega := by
  constructor
  · intro hinclude s hzero hs
    have hop : orthogonalGenuineLimitOperator s = 0 :=
      (orthogonalGenuineLimitOperator_eq_zero_iff s).2 hzero
    have hgreen :
        crossPrimeAlignedGreenLimitVector p q s = 0 :=
      hinclude hs hop
    have hcritical : criticalDisplacement s.re = 0 :=
      (crossPrimeAlignedGreenLimitVector_eq_zero_iff_criticalDisplacement_eq_zero
        p q hp hq hs).1 hgreen
    have hflux :=
      alignedGenuineGreenFlux_tendsto_zero_of_criticalDisplacement
        p hp hs hzero hcritical
    exact
      (seededTfvdGreenRadialClosureAt_iff_coupledGreenFlux_tendsto_zero_of_genuine_zero
        p hp hkappa omega homega hs hzero).2 hflux
  · intro hclosure s hs hop
    have hzero : genuineContinuation s = 0 :=
      (orthogonalGenuineLimitOperator_eq_zero_iff s).1 hop
    have hseeded :
        SeededTfvdGreenRadialClosureAt p kappa omega s :=
      hclosure hzero hs
    have hflux :=
      (seededTfvdGreenRadialClosureAt_iff_coupledGreenFlux_tendsto_zero_of_genuine_zero
        p hp hkappa omega homega hs hzero).1 hseeded
    have hcritical : criticalDisplacement s.re = 0 :=
      criticalDisplacement_eq_zero_of_alignedGenuineGreenFlux_tendsto_zero
        p hp hs hzero hflux
    exact
      (crossPrimeAlignedGreenLimitVector_eq_zero_iff_criticalDisplacement_eq_zero
        p q hp hq hs).2 hcritical

/-! ## Alcance exato da valvula livre -/

/-- O retorno vertical realiza todo dado de bordo: sem a condicao Genuine,
o conjunto de valores caracteristicos da valvula livre e o plano complexo
inteiro. -/
theorem primeCarryWeightedVerticalFreeCharacteristicSet_eq_univ
    (p : ℕ) (hp : 2 ≤ p) :
    {lambda : ℂ |
      (primeCarryWeightedVerticalBoundaryPencil p).IsCharacteristicValue
        lambda} = Set.univ := by
  ext lambda
  simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact
    primeCarryWeightedVerticalBoundaryPencil_everyValue_isCharacteristic
      p hp lambda

end

end CPFormal.Analytic.Cp
