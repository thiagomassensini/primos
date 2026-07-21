import CPFormal.Analytic.CpNativeGpreTowerNorm

/-!
# Cotas aritmeticas nativas para o lift G_pre

Este modulo continua a construcao concreta da torre nativa. A primeira camada
identifica o canal Jordan como uma funcao multiplicativa, calcula seu valor
em potencias primas e prova as cotas `0 <= J_(2*tau)(n) <= n^(2*tau)`.
Nenhuma hipotese espectral ou lei Green entra aqui.
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

/-- O valor do canal Jordan na unidade vem da multiplicatividade. -/
@[simp] theorem nativeGpreJordanArithmetic_one (tau : ℕ) :
    nativeGpreJordanArithmetic tau 1 = 1 :=
  (isMultiplicative_nativeGpreJordanArithmetic tau).map_one

/-- O perfil bruto cresce ao subir um nivel de uma torre prima. -/
theorem nativeGprePrimePowerProfile_mono
    (p tau i : ℕ) (hp : p.Prime) :
    (((p ^ i : ℕ) : ℤ) ^ (2 * tau)) ≤
      (((p ^ (i + 1) : ℕ) : ℤ) ^ (2 * tau)) := by
  exact_mod_cast Nat.pow_le_pow_left
    ((Nat.pow_le_pow_iff_right hp.one_lt).2 (Nat.le_succ i)) (2 * tau)

/-- O canal Jordan e nao negativo em toda potencia prima. -/
theorem nativeGpreJordanArithmetic_prime_pow_nonneg
    (p tau i : ℕ) (hp : p.Prime) :
    0 ≤ nativeGpreJordanArithmetic tau (p ^ i) := by
  cases i with
  | zero => simp
  | succ i =>
      rw [nativeGpreJordanArithmetic_prime_pow_succ p tau i hp]
      exact sub_nonneg.mpr (nativeGprePrimePowerProfile_mono p tau i hp)

/-- Em potencias primas, o canal Jordan nao excede o perfil bruto. -/
theorem nativeGpreJordanArithmetic_prime_pow_le
    (p tau i : ℕ) (hp : p.Prime) :
    nativeGpreJordanArithmetic tau (p ^ i) ≤
      (((p ^ i : ℕ) : ℤ) ^ (2 * tau)) := by
  cases i with
  | zero => simp
  | succ i =>
      rw [nativeGpreJordanArithmetic_prime_pow_succ p tau i hp]
      exact sub_le_self _ (by positivity)

/-- Positividade global do canal Jordan, obtida pela fatoracao multiplicativa
em potencias primas. -/
theorem nativeGpreJordanArithmetic_nonneg (tau n : ℕ) :
    0 ≤ nativeGpreJordanArithmetic tau n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simpa only [
      (isMultiplicative_nativeGpreJordanArithmetic tau).multiplicative_factorization
        _ hn] using!
      Finset.prod_nonneg fun p hp_mem =>
        nativeGpreJordanArithmetic_prime_pow_nonneg p tau _
          (Nat.prime_of_mem_primeFactors hp_mem)

/-- Cota global do canal Jordan pelo perfil bruto. -/
theorem nativeGpreJordanArithmetic_le_powerArithmetic (tau n : ℕ) :
    nativeGpreJordanArithmetic tau n ≤ nativeGprePowerArithmetic tau n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [
      (isMultiplicative_nativeGpreJordanArithmetic tau).multiplicative_factorization
        _ hn,
      (isMultiplicative_nativeGprePowerArithmetic tau).multiplicative_factorization
        _ hn]
    unfold Finsupp.prod
    apply Finset.prod_le_prod
    · intro p hp_mem
      exact nativeGpreJordanArithmetic_prime_pow_nonneg p tau _
        (Nat.prime_of_mem_primeFactors hp_mem)
    · intro p hp_mem
      have hp := Nat.prime_of_mem_primeFactors hp_mem
      rw [nativeGprePowerArithmetic_apply tau (p ^ n.factorization p)
        (pow_ne_zero _ hp.ne_zero)]
      exact nativeGpreJordanArithmetic_prime_pow_le p tau _ hp

/-- Forma numerica da cota global para entradas positivas. -/
theorem nativeGpreJordanArithmetic_le_pow
    (tau n : ℕ) (hn : n ≠ 0) :
    nativeGpreJordanArithmetic tau n ≤ (n : ℤ) ^ (2 * tau) := by
  simpa [nativeGprePowerArithmetic_apply tau n hn] using
    nativeGpreJordanArithmetic_le_powerArithmetic tau n

end

end CPFormal.Analytic.Cp
