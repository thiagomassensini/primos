import CPFormal.Analytic.CpNativeCarryRealOperatorZero
import CPFormal.Analytic.CpNativeCarryRealPlaneComplexPackaging
import Mathlib.Analysis.Complex.Basic

/-!
# O operador complexo é o mesmo operador real

O empacotamento complexo `nativeCarryRealPlaneComplexPackaging` guarda o par real
`(x,y)` nos dois campos de um número complexo.  Já está provado que ele é um
homomorfismo aditivo **injetivo**, que **preserva a energia** (`normSq = energy`)
e que **comuta com toda a câmera finita**.  A unidade imaginária não multiplica
nada: `√-1` é um apêndice, um recipiente de duas coordenadas.

Como `ℂ ≃L[ℝ] ℝ × ℝ` é um homeomorfismo (`Complex.equivRealProdCLM`), o
empacotamento também transporta o **limite** de fronteira. Assim o operador
complexo tem exatamente a mesma condição de fechamento que o operador real
nativo. Logo é, ao pé da letra, o mesmo operador.

Consequência:

`zero complexo (camera,σ,t) ⟺ zero real (camera,σ,t)`.

Essa equivalência vale para todo `sigma`; a coordenada imaginária não cria nem
remove zeros. A rigidez quadrática `sigma = 1 / 2` é um teorema separado sobre
a compatibilidade entre amplitude e massa de carry. Ela não faz parte da
definição de zero.

Quando `sigma ≠ 1 / 2`, o deslocamento é registrado separadamente pelo centro
Green e pelo canal Green completado. Isso não altera o fato de que anulação
continua significando anulação.

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

/-- Zero complexo significa apenas fechamento da fronteira complexa. -/
def IsNativeCarryComplexOperatorZero
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  NativeCarryComplexOperatorBoundaryClosesAt camera sigma time

/-- O predicado de zero complexo não acrescenta nenhuma condição radial. -/
@[simp] theorem isNativeCarryComplexOperatorZero_iff_boundaryClosesAt
    (camera : ℕ) (sigma time : ℝ) :
    IsNativeCarryComplexOperatorZero camera sigma time ↔
      NativeCarryComplexOperatorBoundaryClosesAt camera sigma time :=
  Iff.rfl

/-- **É o mesmo operador.**  O zero complexo e o zero real coincidem. -/
theorem isNativeCarryComplexOperatorZero_iff_real
    (camera : ℕ) (sigma time : ℝ) :
    IsNativeCarryComplexOperatorZero camera sigma time ↔
      IsNativeCarryRealOperatorZero camera sigma time := by
  unfold IsNativeCarryComplexOperatorZero IsNativeCarryRealOperatorZero
  exact nativeCarryComplexOperatorBoundaryClosesAt_iff camera sigma time

end

end CPFormal.Analytic.Cp
