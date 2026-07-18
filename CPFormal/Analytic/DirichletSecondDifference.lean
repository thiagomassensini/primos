import CPFormal.Analytic.CenteredSecondDifferenceBound
import CPFormal.Analytic.CpFiniteDirichletChart
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Segunda diferenca do monomio de Dirichlet

Este arquivo especializa o ganho abstrato da segunda diferenca a

`f_s(x) = x^(-s)`, para `x > 0`.

A segunda derivada e

`s * (s + 1) * x^(-s-2)`.

Consequentemente, quando `re(s) > -1`, cada bracket centrado satisfaz uma
cota por uma constante vezes `x^(-re(s)-2)`. Esta e a estimativa analitica
que alimenta a comparacao posterior com uma p-serie.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

local instance : NormedSpace ℝ ℂ := NormedSpace.complexToReal

/-- O monomio de Dirichlet visto como funcao de uma variavel real positiva. -/
def realDirichletPower (s : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (-s)

/-- Primeira derivada formal de `realDirichletPower`. -/
def realDirichletPowerDeriv (s : ℂ) (x : ℝ) : ℂ :=
  (-s) * (x : ℂ) ^ (-s - 1)

/-- Segunda derivada formal de `realDirichletPower`. -/
def realDirichletPowerDeriv2 (s : ℂ) (x : ℝ) : ℂ :=
  s * (s + 1) * (x : ℂ) ^ (-s - 2)

/-- Derivada de `x^(-s)` no eixo real positivo, no caso nao constante. -/
theorem hasDerivAt_realDirichletPower
    {s : ℂ} (hs : s ≠ 0) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (realDirichletPower s)
      (realDirichletPowerDeriv s x) x := by
  simpa [realDirichletPower, realDirichletPowerDeriv] using
    (hasDerivAt_ofReal_cpow_const (ne_of_gt hx) (neg_ne_zero.mpr hs))

/-- A segunda derivada existe em todo ponto positivo quando `re(s)>-1`. -/
theorem hasDerivAt_realDirichletPowerDeriv
    {s : ℂ} (hs : -1 < s.re) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (realDirichletPowerDeriv s)
      (realDirichletPowerDeriv2 s x) x := by
  have hexponent : -s - 1 ≠ 0 := by
    intro h
    have hre : -s.re - 1 = 0 := by
      simpa using congrArg Complex.re h
    linarith
  have hpow :=
    hasDerivAt_ofReal_cpow_const (ne_of_gt hx) hexponent
  have hexponentSub : (-s - 1) - 1 = -s - 2 := by ring
  have hcoefficient : (-s) * (-s - 1) = s * (s + 1) := by ring
  simpa only [realDirichletPowerDeriv, realDirichletPowerDeriv2,
    hexponentSub, ← mul_assoc, hcoefficient] using hpow.const_mul (-s)

/-- Norma exata da segunda derivada sobre o eixo real positivo. -/
theorem norm_realDirichletPowerDeriv2
    (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖realDirichletPowerDeriv2 s x‖ =
      ‖s * (s + 1)‖ * x ^ (-s.re - 2) := by
  rw [realDirichletPowerDeriv2, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  congr 1

/-!
O ganho concreto: a braquetada compra duas potencias. A base da cota e o
menor ponto do segmento, `center-radius`, pois o expoente real
`-re(s)-2` e negativo em todo o dominio `re(s)>-1`.
-/
theorem norm_realDirichletPower_centeredSecondDifference_le
    {s : ℂ} (hs : -1 < s.re)
    {center radius : ℝ}
    (hradius : 0 ≤ radius)
    (hleft : 0 < center - radius) :
    ‖realDirichletPower s (center - radius) -
        (2 • realDirichletPower s center) +
          realDirichletPower s (center + radius)‖ ≤
      2 *
        (‖s * (s + 1)‖ *
          (center - radius) ^ (-s.re - 2)) *
        radius ^ 2 := by
  by_cases hs0 : s = 0
  · subst s
    norm_num [realDirichletPower, two_smul]
  · refine norm_centeredSecondDifference_le
      (f := realDirichletPower s)
      (f' := realDirichletPowerDeriv s)
      (f'' := realDirichletPowerDeriv2 s)
      (lower := center - radius)
      (C := ‖s * (s + 1)‖ *
        (center - radius) ^ (-s.re - 2))
      hradius le_rfl ?_ ?_ ?_
    · intro x hx
      exact hasDerivAt_realDirichletPower hs0 (lt_of_lt_of_le hleft hx)
    · intro x hx
      exact hasDerivAt_realDirichletPowerDeriv hs
        (lt_of_lt_of_le hleft hx)
    · intro x hx
      rw [norm_realDirichletPowerDeriv2 s (lt_of_lt_of_le hleft hx)]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hleft hx (by linarith [hs]))
        (norm_nonneg _)

end

end CPFormal.Analytic.Cp
