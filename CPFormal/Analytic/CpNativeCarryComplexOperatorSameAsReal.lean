import CPFormal.Analytic.CpNativeCarryRealOperatorConfinement
import CPFormal.Analytic.CpNativeCarryRealPlaneComplexPackaging
import Mathlib.Analysis.Complex.Basic

/-!
# O operador complexo é o mesmo operador real: confinamento por troca de roupa

O empacotamento complexo `nativeCarryRealPlaneComplexPackaging` guarda o par real
`(x,y)` nos dois campos de um número complexo.  Já está provado que ele é um
homomorfismo aditivo **injetivo**, que **preserva a energia** (`normSq = energy`)
e que **comuta com toda a câmera finita**.  A unidade imaginária não multiplica
nada: `√-1` é um apêndice, um recipiente de duas coordenadas.

Como `ℂ ≃L[ℝ] ℝ × ℝ` é um homeomorfismo (`Complex.equivRealProdCLM`), o
empacotamento também transporta o **limite** de fronteira.  Assim o operador
complexo tem exatamente a mesma condição de fechamento que o operador real
nativo, e o mesmo domínio de massa.  Logo é, ao pé da letra, o mesmo operador.

Consequência (ligando os teoremas já provados):

`zero do operador complexo (camera,σ,t) ⟺ zero do operador real (camera,σ,t)`
`⟹ σ = 1/2`.

Portanto o operador Genuine complexo **completo** não tem zero fora do expoente
autodual — não por um argumento novo, mas porque é o operador real de sempre com
outra roupa.

Aviso honesto: isto vale para o operador **completo** (que carrega o dado de
massa via o domínio).  Não afirma que o escalar Genuine comprimido sozinho
(`genuineContinuation`) reconstrua a massa que a compressão descartou — esse é o
ângulo cego, e continua sendo a única seta não automática.

Genuine First: nenhum zeta, equação funcional ou RH.
-/

open scoped Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-- O empacotamento é a inversa do homeomorfismo canônico `ℂ ≃L[ℝ] ℝ × ℝ`. -/
theorem nativeCarryRealPlaneComplexPackaging_eq_equivRealProdCLM_symm :
    nativeCarryRealPlaneComplexPackaging = ⇑Complex.equivRealProdCLM.symm := by
  funext u
  rw [Complex.equivRealProdCLM_symm_apply]
  apply Complex.ext <;> simp [nativeCarryRealPlaneComplexPackaging]

/--
Fechamento de fronteira do operador **complexo**: o resultante finito empacotado
converge para `0` em `ℂ`.
-/
def NativeCarryComplexOperatorBoundaryClosesAt
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  Tendsto
    (fun cutoff : ℕ =>
      nativeCarryRealPlaneComplexPackaging
        (nativeCarryRealPlaneFiniteChartAt camera cutoff sigma time))
    atTop (nhds 0)

/--
A fronteira complexa fecha exatamente quando a fronteira real fecha: o
empacotamento é um homeomorfismo, então preserva o limite.
-/
theorem nativeCarryComplexOperatorBoundaryClosesAt_iff
    (camera : ℕ) (sigma time : ℝ) :
    NativeCarryComplexOperatorBoundaryClosesAt camera sigma time ↔
      NativeCarryRealOperatorBoundaryClosesAt camera sigma time := by
  unfold NativeCarryComplexOperatorBoundaryClosesAt
    NativeCarryRealOperatorBoundaryClosesAt
  rw [nativeCarryRealPlaneComplexPackaging_eq_equivRealProdCLM_symm]
  have h0 : (Complex.equivRealProdCLM.symm 0 : ℂ) = 0 := map_zero _
  rw [← h0]
  exact
    (Complex.equivRealProdCLM.symm.toHomeomorph.isEmbedding.tendsto_nhds_iff).symm

/--
Zero do operador **complexo** completo: mesma massa de carry no domínio e
fechamento de fronteira complexo.
-/
def IsNativeCarryComplexOperatorZero
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  NativeCarryRealPlaneMassCompatible sigma time ∧
    NativeCarryComplexOperatorBoundaryClosesAt camera sigma time

/-- **É o mesmo operador.**  O zero complexo e o zero real coincidem. -/
theorem isNativeCarryComplexOperatorZero_iff_real
    (camera : ℕ) (sigma time : ℝ) :
    IsNativeCarryComplexOperatorZero camera sigma time ↔
      IsNativeCarryRealOperatorZero camera sigma time := by
  unfold IsNativeCarryComplexOperatorZero IsNativeCarryRealOperatorZero
  rw [nativeCarryComplexOperatorBoundaryClosesAt_iff]

/--
Fatoração exata do operador complexo, herdada do operador real:
`Zero_camera = {1/2} × Resonance_camera`.
-/
theorem isNativeCarryComplexOperatorZero_iff
    (camera : ℕ) (sigma time : ℝ) :
    IsNativeCarryComplexOperatorZero camera sigma time ↔
      sigma = (1 : ℝ) / 2 ∧
        IsNativeCarryRealOperatorResonance camera time := by
  rw [isNativeCarryComplexOperatorZero_iff_real,
    isNativeCarryRealOperatorZero_iff]

/--
**Confinamento do operador Genuine complexo completo.**  Todo zero tem o
expoente autodual `σ = 1/2` — porque é literalmente o operador real nativo,
apenas empacotado em `ℂ`.
-/
theorem nativeCarryComplexOperatorZero_sigma_eq_half
    {camera : ℕ} {sigma time : ℝ}
    (hzero : IsNativeCarryComplexOperatorZero camera sigma time) :
    sigma = (1 : ℝ) / 2 :=
  nativeCarryRealOperatorZero_sigma_eq_half
    ((isNativeCarryComplexOperatorZero_iff_real camera sigma time).1 hzero)

/-- Não há zero do operador complexo numa casca radial fora do autodual. -/
theorem nativeCarryComplexOperatorZero_ne_of_sigma_ne_half
    {camera : ℕ} {sigma time : ℝ}
    (hoff : sigma ≠ (1 : ℝ) / 2) :
    ¬ IsNativeCarryComplexOperatorZero camera sigma time := by
  intro hzero
  exact hoff (nativeCarryComplexOperatorZero_sigma_eq_half hzero)

end

end CPFormal.Analytic.Cp
