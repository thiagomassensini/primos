import CPFormal.Analytic.CpNativeGpreTowerNorm
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Cotas aritmeticas nativas para o lift G_pre

Este modulo continua a construcao concreta da torre nativa. A primeira camada
identifica o canal Jordan como uma funcao multiplicativa, calcula seu valor
em potencias primas e prova as cotas `0 <= J_(2*tau)(n) <= n^(2*tau)`.

A segunda camada empacota simultaneamente o perfil de potencia e sua
coordenada de valuacao numa extensao quadrado-zero. A convolucao de Moebius
nesse anel possui como primeira coordenada `J_(2*tau)` e como coordenada
tangente `H_(p,tau)`. O kernel obtem assim a regra de Leibniz coprima, a
positividade global de `H`, sua cota pelo perfil bruto e, finalmente, o
majorante local do bracket de Jordan usado pelo ledger da norma.

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
    simp only [Finsupp.prod]
    apply Finset.prod_le_prod
    · intro p hp_mem
      exact nativeGpreJordanArithmetic_prime_pow_nonneg p tau _
        (Nat.prime_of_mem_primeFactors hp_mem)
    · intro p hp_mem
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
      have hpow : p ^ n.factorization p ≠ 0 := pow_ne_zero _ hp.ne_zero
      rw [nativeGprePowerArithmetic_apply tau _ hpow]
      exact nativeGpreJordanArithmetic_prime_pow_le p tau _ hp

/-- Forma numerica da cota global para entradas positivas. -/
theorem nativeGpreJordanArithmetic_le_pow
    (tau n : ℕ) (hn : n ≠ 0) :
    nativeGpreJordanArithmetic tau n ≤ (n : ℤ) ^ (2 * tau) := by
  simpa only [nativeGprePowerArithmetic_apply tau n hn] using
    nativeGpreJordanArithmetic_le_powerArithmetic tau n

/-!
## Extensao dual e regra de Leibniz do canal H
-/

/-- Anel dual inteiro. A primeira coordenada guarda o perfil de potencia; a
segunda guarda sua derivada na direcao da valuacao `v_p`. -/
abbrev NativeGpreDualInteger := TrivSqZeroExt ℤ ℤ

/-- Perfil multiplicativo dual `(n^(2*tau), v_p(n) n^(2*tau))`. -/
def nativeGpreDualPowerArithmetic
    (p tau : ℕ) : ArithmeticFunction NativeGpreDualInteger :=
  ⟨fun n =>
      (nativeGprePowerArithmetic tau n,
        nativeGpreValuationPowerArithmetic p tau n),
    rfl⟩

@[simp] theorem nativeGpreDualPowerArithmetic_fst
    (p tau n : ℕ) :
    (nativeGpreDualPowerArithmetic p tau n).fst =
      nativeGprePowerArithmetic tau n := rfl

@[simp] theorem nativeGpreDualPowerArithmetic_snd
    (p tau n : ℕ) :
    (nativeGpreDualPowerArithmetic p tau n).snd =
      nativeGpreValuationPowerArithmetic p tau n := rfl

/-- O par potencia--valuacao e multiplicativo no anel dual: a segunda
coordenada satisfaz exatamente a regra do produto. -/
theorem isMultiplicative_nativeGpreDualPowerArithmetic
    (p tau : ℕ) :
    IsMultiplicative (nativeGpreDualPowerArithmetic p tau) := by
  rw [IsMultiplicative.iff_ne_zero]
  constructor
  · apply TrivSqZeroExt.ext <;> simp [nativeGpreDualPowerArithmetic]
  · intro a b ha hb hab
    apply TrivSqZeroExt.ext
    · exact (isMultiplicative_nativeGprePowerArithmetic tau).map_mul_of_coprime hab
    · change
        nativeGpreValuationPowerArithmetic p tau (a * b) =
          nativeGprePowerArithmetic tau a *
              nativeGpreValuationPowerArithmetic p tau b +
            nativeGpreValuationPowerArithmetic p tau a *
              nativeGprePowerArithmetic tau b
      have hfacNat :
          (a * b).factorization p =
            a.factorization p + b.factorization p := by
        simpa using congrArg (fun f : ℕ →₀ ℕ => f p)
          (Nat.factorization_mul ha hb)
      have hfacInt :
          ((a * b).factorization p : ℤ) =
            (a.factorization p : ℤ) + (b.factorization p : ℤ) := by
        exact_mod_cast hfacNat
      rw [nativeGpreValuationPowerArithmetic_apply p tau (a * b)
          (mul_ne_zero ha hb),
        nativeGprePowerArithmetic_apply tau a ha,
        nativeGprePowerArithmetic_apply tau b hb,
        nativeGpreValuationPowerArithmetic_apply p tau a ha,
        nativeGpreValuationPowerArithmetic_apply p tau b hb,
        hfacInt]
      push_cast
      rw [mul_pow]
      ring

/-- Convolucao de Moebius do perfil dual. -/
def nativeGpreDualJordanArithmetic
    (p tau : ℕ) : ArithmeticFunction NativeGpreDualInteger :=
  (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) :
      ArithmeticFunction NativeGpreDualInteger) *
    nativeGpreDualPowerArithmetic p tau)

/-- A primeira coordenada da convolucao dual e o canal Jordan. -/
@[simp] theorem nativeGpreDualJordanArithmetic_fst
    (p tau n : ℕ) :
    (nativeGpreDualJordanArithmetic p tau n).fst =
      nativeGpreJordanArithmetic tau n := by
  classical
  unfold nativeGpreDualJordanArithmetic nativeGpreJordanArithmetic
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  rw [TrivSqZeroExt.fst_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp [nativeGpreDualPowerArithmetic]

/-- A coordenada tangente da convolucao dual e literalmente `H_(p,tau)`. -/
@[simp] theorem nativeGpreDualJordanArithmetic_snd
    (p tau n : ℕ) :
    (nativeGpreDualJordanArithmetic p tau n).snd =
      nativeGpreHArithmetic p tau n := by
  classical
  unfold nativeGpreDualJordanArithmetic nativeGpreHArithmetic
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  rw [TrivSqZeroExt.snd_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp [nativeGpreDualPowerArithmetic]

/-- A convolucao dual inteira e multiplicativa. Em particular, `H` e a
coordenada tangente de um objeto multiplicativo, embora nao seja multiplicativo
sozinho. -/
theorem isMultiplicative_nativeGpreDualJordanArithmetic
    (p tau : ℕ) :
    IsMultiplicative (nativeGpreDualJordanArithmetic p tau) := by
  exact ArithmeticFunction.isMultiplicative_moebius.intCast.mul
    (isMultiplicative_nativeGpreDualPowerArithmetic p tau)

/-- Regra de Leibniz coprima do canal `H` sobre o canal Jordan. -/
theorem nativeGpreHArithmetic_coprime_mul
    (p tau a b : ℕ) (hab : a.Coprime b) :
    nativeGpreHArithmetic p tau (a * b) =
      nativeGpreJordanArithmetic tau a * nativeGpreHArithmetic p tau b +
        nativeGpreHArithmetic p tau a * nativeGpreJordanArithmetic tau b := by
  have hdual :=
    (isMultiplicative_nativeGpreDualJordanArithmetic p tau).map_mul_of_coprime hab
  have hsnd := congrArg TrivSqZeroExt.snd hdual
  simpa using hsnd

/-!
## Positividade e majorantes do canal H
-/

/-- Em uma potencia prima positiva, `H` e a diferenca de dois perfis de
valuacao consecutivos. -/
theorem nativeGpreHArithmetic_prime_pow_succ
    (p q tau i : ℕ) (hq : q.Prime) :
    nativeGpreHArithmetic p tau (q ^ (i + 1)) =
      nativeGpreValuationPowerArithmetic p tau (q ^ (i + 1)) -
        nativeGpreValuationPowerArithmetic p tau (q ^ i) := by
  have hcurr := sum_divisors_nativeGpreHArithmetic
    p tau (q ^ (i + 1)) (pow_ne_zero _ hq.ne_zero)
  have hprev := sum_divisors_nativeGpreHArithmetic
    p tau (q ^ i) (pow_ne_zero _ hq.ne_zero)
  rw [Nat.sum_divisors_prime_pow hq] at hcurr hprev
  rw [Finset.sum_range_succ] at hcurr
  rw [nativeGpreValuationPowerArithmetic_apply p tau (q ^ (i + 1))
      (pow_ne_zero _ hq.ne_zero),
    nativeGpreValuationPowerArithmetic_apply p tau (q ^ i)
      (pow_ne_zero _ hq.ne_zero)]
  linarith

/-- O perfil bruto de valuacao nao diminui ao subir uma potencia prima. -/
theorem nativeGpreValuationPowerArithmetic_prime_pow_mono
    (p q tau i : ℕ) (hp : p.Prime) (hq : q.Prime) :
    nativeGpreValuationPowerArithmetic p tau (q ^ i) ≤
      nativeGpreValuationPowerArithmetic p tau (q ^ (i + 1)) := by
  by_cases hpq : p = q
  · subst p
    rw [nativeGpreValuationPowerArithmetic_apply q tau (q ^ i)
        (pow_ne_zero _ hq.ne_zero),
      nativeGpreValuationPowerArithmetic_apply q tau (q ^ (i + 1))
        (pow_ne_zero _ hq.ne_zero)]
    simp only [hq.factorization_pow, Finsupp.single_eq_same]
    have hprofile := nativeGprePrimePowerProfile_mono q tau i hq
    have hleft :
        (i : ℤ) * (((q ^ i : ℕ) : ℤ) ^ (2 * tau)) ≤
          (i : ℤ) * (((q ^ (i + 1) : ℕ) : ℤ) ^ (2 * tau)) :=
      mul_le_mul_of_nonneg_left hprofile (by positivity)
    have hright :
        (i : ℤ) * (((q ^ (i + 1) : ℕ) : ℤ) ^ (2 * tau)) ≤
          ((i + 1 : ℕ) : ℤ) *
            (((q ^ (i + 1) : ℕ) : ℤ) ^ (2 * tau)) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Nat.le_succ i
      · positivity
    exact hleft.trans hright
  · rw [nativeGpreValuationPowerArithmetic_apply p tau (q ^ i)
        (pow_ne_zero _ hq.ne_zero),
      nativeGpreValuationPowerArithmetic_apply p tau (q ^ (i + 1))
        (pow_ne_zero _ hq.ne_zero)]
    simp [hq.factorization_pow, hpq]

/-- O perfil de valuacao e nao negativo em toda entrada. -/
theorem nativeGpreValuationPowerArithmetic_nonneg
    (p tau n : ℕ) :
    0 ≤ nativeGpreValuationPowerArithmetic p tau n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [nativeGpreValuationPowerArithmetic_apply p tau n hn]
    positivity

/-- Positividade de `H` em toda potencia prima. -/
theorem nativeGpreHArithmetic_prime_pow_nonneg
    (p q tau i : ℕ) (hp : p.Prime) (hq : q.Prime) :
    0 ≤ nativeGpreHArithmetic p tau (q ^ i) := by
  cases i with
  | zero =>
      have hone :=
        (isMultiplicative_nativeGpreDualJordanArithmetic p tau).map_one
      have hsnd := congrArg TrivSqZeroExt.snd hone
      rw [nativeGpreDualJordanArithmetic_snd] at hsnd
      have hzero : nativeGpreHArithmetic p tau 1 = 0 := by
        simpa using hsnd
      simpa [hzero]
  | succ i =>
      rw [nativeGpreHArithmetic_prime_pow_succ p q tau i hq]
      exact sub_nonneg.mpr
        (nativeGpreValuationPowerArithmetic_prime_pow_mono p q tau i hp hq)

/-- A coordenada `H` nao excede o perfil bruto na mesma potencia prima. -/
theorem nativeGpreHArithmetic_prime_pow_le
    (p q tau i : ℕ) (hp : p.Prime) (hq : q.Prime) :
    nativeGpreHArithmetic p tau (q ^ i) ≤
      nativeGpreValuationPowerArithmetic p tau (q ^ i) := by
  cases i with
  | zero =>
      have hone :=
        (isMultiplicative_nativeGpreDualJordanArithmetic p tau).map_one
      have hsnd := congrArg TrivSqZeroExt.snd hone
      rw [nativeGpreDualJordanArithmetic_snd] at hsnd
      have hzero : nativeGpreHArithmetic p tau 1 = 0 := by
        simpa using hsnd
      simpa [hzero] using
        nativeGpreValuationPowerArithmetic_nonneg p tau 1
  | succ i =>
      rw [nativeGpreHArithmetic_prime_pow_succ p q tau i hq]
      exact sub_le_self _
        (nativeGpreValuationPowerArithmetic_nonneg p tau (q ^ i))

/-- Produtos finitos de numeros duais com duas coordenadas nao negativas
continuam nao negativos em ambas as coordenadas. -/
theorem nativeGpreDualProduct_nonneg
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → NativeGpreDualInteger)
    (hf : ∀ i ∈ S, 0 ≤ (f i).fst ∧ 0 ≤ (f i).snd) :
    0 ≤ (∏ i ∈ S, f i).fst ∧ 0 ≤ (∏ i ∈ S, f i).snd := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      rw [Finset.prod_insert ha]
      have haNon := hf a (Finset.mem_insert_self a S)
      have hS : ∀ i ∈ S, 0 ≤ (f i).fst ∧ 0 ≤ (f i).snd := by
        intro i hi
        exact hf i (Finset.mem_insert_of_mem hi)
      have ihNon := ih hS
      constructor
      · exact mul_nonneg haNon.1 ihNon.1
      · change
          0 ≤ (f a).fst * (∏ i ∈ S, f i).snd +
            (f a).snd * (∏ i ∈ S, f i).fst
        exact add_nonneg
          (mul_nonneg haNon.1 ihNon.2)
          (mul_nonneg haNon.2 ihNon.1)

/-- Positividade global de `H`, obtida da fatoracao multiplicativa no anel
dual. -/
theorem nativeGpreHArithmetic_nonneg
    (p tau n : ℕ) (hp : p.Prime) :
    0 ≤ nativeGpreHArithmetic p tau n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [nativeGpreHArithmetic]
  · rw [← nativeGpreDualJordanArithmetic_snd]
    have hfactor := (isMultiplicative_nativeGpreDualJordanArithmetic p tau).multiplicative_factorization n hn
    rw [hfactor]
    exact (nativeGpreDualProduct_nonneg n.primeFactors
      (fun q => nativeGpreDualJordanArithmetic p tau
        (q ^ n.factorization q)) (by
          intro q hqmem
          have hq : q.Prime := Nat.prime_of_mem_primeFactors hqmem
          constructor
          · rw [nativeGpreDualJordanArithmetic_fst]
            exact nativeGpreJordanArithmetic_prime_pow_nonneg
              q tau (n.factorization q) hq
          · rw [nativeGpreDualJordanArithmetic_snd]
            exact nativeGpreHArithmetic_prime_pow_nonneg
              p q tau (n.factorization q) hp hq)).2

/-- Como a soma de `H` nos divisores e o perfil bruto e todos os somadores
sao nao negativos, cada coordenada individual e dominada por esse perfil. -/
theorem nativeGpreHArithmetic_le_valuationPowerArithmetic
    (p tau n : ℕ) (hp : p.Prime) :
    nativeGpreHArithmetic p tau n ≤
      nativeGpreValuationPowerArithmetic p tau n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [nativeGpreHArithmetic]
  · have hle :
        nativeGpreHArithmetic p tau n ≤
          ∑ d ∈ n.divisors, nativeGpreHArithmetic p tau d :=
      Finset.single_le_sum
        (fun d hd => nativeGpreHArithmetic_nonneg p tau d hp)
        (Nat.mem_divisors_self n hn)
    rw [sum_divisors_nativeGpreHArithmetic p tau n hn] at hle
    simpa [nativeGpreValuationPowerArithmetic_apply p tau n hn] using hle

/-- Um divisor comum nao pode carregar mais que metade da valuacao total das
duas pernas. -/
theorem two_mul_factorization_le_nativeGprePairValuation
    (u v p d : ℕ) (hu : u ≠ 0) (hv : v ≠ 0) (hd0 : d ≠ 0)
    (hd : d ∣ Nat.gcd u v) :
    2 * (d.factorization p : ℤ) ≤ nativeGprePairValuation u v p := by
  have hdu : d ∣ u := hd.trans (Nat.gcd_dvd_left u v)
  have hdv : d ∣ v := hd.trans (Nat.gcd_dvd_right u v)
  have hleuNat : d.factorization p ≤ u.factorization p :=
    ((Nat.factorization_le_iff_dvd hd0 hu).2 hdu) p
  have hlevNat : d.factorization p ≤ v.factorization p :=
    ((Nat.factorization_le_iff_dvd hd0 hv).2 hdv) p
  have hleu : (d.factorization p : ℤ) ≤ (u.factorization p : ℤ) := by
    exact_mod_cast hleuNat
  have hlev : (d.factorization p : ℤ) ≤ (v.factorization p : ℤ) := by
    exact_mod_cast hlevNat
  unfold nativeGprePairValuation
  linarith

/-- Majorante local central do ledger. Para todo divisor Jordan do gcd, os
dois termos nao negativos do bracket pertencem ao mesmo intervalo
`[0, a_p d^(2*tau)]`; portanto sua diferenca tem modulo no maximo esse
endpoint. -/
theorem abs_nativeGpreJordanBracket_le
    (u v p tau d : ℕ) (hp : p.Prime)
    (hu : u ≠ 0) (hv : v ≠ 0) (hd0 : d ≠ 0)
    (hd : d ∣ Nat.gcd u v) :
    |nativeGpreJordanBracket u v p tau d| ≤
      nativeGprePairValuation u v p * (d : ℤ) ^ (2 * tau) := by
  have hJ0 := nativeGpreJordanArithmetic_nonneg tau d
  have hJle := nativeGpreJordanArithmetic_le_pow tau d hd0
  have hH0 := nativeGpreHArithmetic_nonneg p tau d hp
  have hHle := nativeGpreHArithmetic_le_valuationPowerArithmetic p tau d hp
  rw [nativeGpreValuationPowerArithmetic_apply p tau d hd0] at hHle
  have hval := two_mul_factorization_le_nativeGprePairValuation
    u v p d hu hv hd0 hd
  have hA0 : 0 ≤ nativeGprePairValuation u v p := by
    unfold nativeGprePairValuation
    positivity
  have hP0 : 0 ≤ (d : ℤ) ^ (2 * tau) := by positivity
  have hJA0 :
      0 ≤ nativeGpreJordanArithmetic tau d *
        nativeGprePairValuation u v p :=
    mul_nonneg hJ0 hA0
  have hJAle :
      nativeGpreJordanArithmetic tau d *
          nativeGprePairValuation u v p ≤
        nativeGprePairValuation u v p * (d : ℤ) ^ (2 * tau) := by
    calc
      nativeGpreJordanArithmetic tau d * nativeGprePairValuation u v p ≤
          (d : ℤ) ^ (2 * tau) * nativeGprePairValuation u v p :=
        mul_le_mul_of_nonneg_right hJle hA0
      _ = nativeGprePairValuation u v p * (d : ℤ) ^ (2 * tau) := by ring
  have h2H0 : 0 ≤ 2 * nativeGpreHArithmetic p tau d := by positivity
  have h2Hle :
      2 * nativeGpreHArithmetic p tau d ≤
        nativeGprePairValuation u v p * (d : ℤ) ^ (2 * tau) := by
    calc
      2 * nativeGpreHArithmetic p tau d ≤
          2 * ((d.factorization p : ℤ) * (d : ℤ) ^ (2 * tau)) :=
        mul_le_mul_of_nonneg_left hHle (by norm_num)
      _ = (2 * (d.factorization p : ℤ)) * (d : ℤ) ^ (2 * tau) := by ring
      _ ≤ nativeGprePairValuation u v p * (d : ℤ) ^ (2 * tau) :=
        mul_le_mul_of_nonneg_right hval hP0
  unfold nativeGpreJordanBracket
  apply (abs_le).2
  constructor <;> linarith

end

end CPFormal.Analytic.Cp
