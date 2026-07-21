import Mathlib.Data.Real.Basic

/-!
# Tipos basicos do carrier `G_pre`

Este modulo minimo separa os rotulos combinatorios do lift aritmetico das
camadas topologica e espectral. Assim, as coordenadas nativas e a completacao
`Qtilde` usam literalmente o mesmo tipo de canto.
-/

namespace CPFormal.Analytic.Cp

/-- Primo da camera aritmetica. -/
structure GpreArithmeticPrime where
  val : ℕ
  deriving Repr, DecidableEq

/-- Tempo inteiro do ledger aritmetico. Nao e a altura espectral. -/
structure GpreArithmeticTime where
  val : ℕ
  deriving Repr, DecidableEq

/-- Divisor resolvido do canal de Jordan. -/
structure GpreJordanDivisor where
  val : ℕ
  deriving Repr, DecidableEq

/-- Primo material da torre enriquecida. -/
structure GpreTowerPrime where
  val : ℕ
  deriving Repr, DecidableEq

/-- Nivel material da torre. Nao e o divisor de Jordan. -/
structure GpreTowerLevel where
  val : ℕ
  deriving Repr, DecidableEq

/-- Os quatro cantos nativos de uma celula C2. -/
inductive GpreCorner where
  | lowerLeft
  | lowerRight
  | upperLeft
  | upperRight
  deriving Repr, DecidableEq

/-- Orientacao original ou completacao reciproca. -/
inductive GpreOrientation where
  | original
  | reciprocal
  deriving Repr, DecidableEq

/-- As duas pernas preservadas antes da forma de bordo. -/
inductive GpreLeg where
  | left
  | right
  deriving Repr, DecidableEq

/-- Papel do canal no par valor--fluxo do grafo. -/
inductive GpreGraphRole where
  | value
  | numberFlux
  deriving Repr, DecidableEq

/-- Contexto discreto completo. Campos semanticamente distintos continuam
distintos no tipo, mesmo quando seus valores subjacentes sao naturais. -/
structure NativeGpreContext where
  arithmeticPrime : GpreArithmeticPrime
  time : GpreArithmeticTime
  cell : ℕ
  corner : GpreCorner
  orientation : GpreOrientation
  role : GpreGraphRole
  leg : GpreLeg
  jordanDivisor : GpreJordanDivisor
  towerPrime : GpreTowerPrime
  towerLevel : GpreTowerLevel
  deriving Repr, DecidableEq

/-- Peso de contagem fixo, anterior ao cutoff e ao parametro espectral. -/
def nativeGpreCountingWeight (_ : NativeGpreContext) : ℝ := 1

@[simp] theorem nativeGpreCountingWeight_eq_one (c : NativeGpreContext) :
    nativeGpreCountingWeight c = 1 := rfl

theorem nativeGpreCountingWeight_pos (c : NativeGpreContext) :
    0 < nativeGpreCountingWeight c := by
  simp

/-- Perfil de torre nativo `p^(-j*tau)/j`, com o nivel zero separado. -/
noncomputable def nativeUnitMassTowerProfile (p tau j : ℕ) : ℝ :=
  if j = 0 then 0 else (((p : ℝ) ^ (j * tau))⁻¹) / (j : ℝ)

@[simp] theorem nativeUnitMassTowerProfile_zero_level (p tau : ℕ) :
    nativeUnitMassTowerProfile p tau 0 = 0 := by
  simp [nativeUnitMassTowerProfile]

@[simp] theorem nativeUnitMassTowerProfile_zero_time
    (p j : ℕ) (hj : j ≠ 0) :
    nativeUnitMassTowerProfile p 0 j = (j : ℝ)⁻¹ := by
  simp [nativeUnitMassTowerProfile, hj, div_eq_mul_inv]

end CPFormal.Analytic.Cp
