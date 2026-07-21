import CPFormal.Analytic.CpNativeGpreTowerNorm

/-!
# Cotas aritmeticas nativas para o lift G_pre

Este modulo continua a construcao concreta da torre nativa. A primeira camada
identifica o canal Jordan como uma funcao multiplicativa, calcula seu valor
em potencias primas e prova sua positividade local. Nenhuma hipotese espectral
ou lei Green entra aqui.
-/

open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius

namespace CPFormal.Analytic.Cp

noncomputable section

open ArithmeticFunction

/-- O perfil inteiro usado por `G_pre` e o cast do perfil aritmetico canonico
`n |-> n^(2*tau)`. -/
theorem nativeGprePowerArithmetic_eq_pow (tau : ℕ) :
    nativeGprePowerArithmetic tau =
      (ArithmeticFunction.pow (2 * tau) : ArithmeticFunction ℤ) := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp [nativeGprePowerArithmetic]
  · simp [nativeGprePowerArithmetic, ArithmeticFunction.pow_apply, hn]

/-- O perfil de potencia e multiplicativo. -/
theorem isMultiplicative_nativeGprePowerArithmetic (tau : ℕ) :
    IsMultiplicative (nativeGprePowerArithmetic tau) := by
  rw [nativeGprePowerArithmetic_eq_pow]
  exact ArithmeticFunction.isMultiplicative_pow.natCast

/-- O canal Jordan nativo e multiplicativo. -/
theorem isMultiplicative_nativeGpreJordanArithmetic (tau : ℕ) :
    IsMultiplicative (nativeGpreJordanArithmetic tau) := by
  exact ArithmeticFunction.isMultiplicative_moebius.mul
    (isMultiplicative_nativeGprePowerArithmetic tau)

/-- Em uma potencia prima positiva, o canal Jordan e a diferenca entre dois
perfis consecutivos. -/
theorem nativeGpreJordanArithmetic_prime_pow_succ
    (p tau i : ℕ) (hp : p.Prime) :
    nativeGpreJordanArithmetic tau (p ^ (i + 1)) =
      (((p ^ (i + 1) : ℕ) : ℤ) ^ (2 * tau) -
        (((p ^ i : ℕ) : ℤ) ^ (2 * tau))) := by
  have hcurr := sum_divisors_nativeGpreJordanArithmetic
    tau (p ^ (i + 1)) (pow_ne_zero _ hp.ne_zero)
  have hprev := sum_divisors_nativeGpreJordanArithmetic
    tau (p ^ i) (pow_ne_zero _ hp.ne_zero)
  rw [Nat.sum_divisors_prime_pow hp] at hcurr hprev
  rw [Finset.sum_range_succ] at hcurr
  linarith

/-- O canal Jordan e nao negativo em toda potencia prima. -/
theorem nativeGpreJordanArithmetic_prime_pow_nonneg
    (p tau i : ℕ) (hp : p.Prime) :
    0 ≤ nativeGpreJordanArithmetic tau (p ^ i) := by
  cases i with
  | zero =>
      simpa [(isMultiplicative_nativeGpreJordanArithmetic tau).map_one]
  | succ i =>
      rw [nativeGpreJordanArithmetic_prime_pow_succ p tau i hp]
      apply sub_nonneg.mpr
      norm_cast
      exact Nat.pow_le_pow_left
        ((Nat.pow_le_pow_iff_right hp.one_lt).2 (Nat.le_succ i)) (2 * tau)

end

end CPFormal.Analytic.Cp
