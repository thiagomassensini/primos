import CPFormal.Analytic.CpNativeGpreTowerNorm
import Mathlib.Analysis.PSeries

/-!
# Somabilidade multiprima da torre nativa de G_pre

Este modulo registra uma consequencia aritmetica independente do programa de
observabilidade Green. Para todo tempo inteiro positivo `tau`, a cota local

`‖nativeGpreTowerProfileVector p tau‖ ^ 2 ≤ (4 / 3) * p ^ (-2 * tau)`

e a convergencia da p-serie em todos os naturais implicam somabilidade dos
quadrados das normas quando `p` percorre `Nat.Primes`.

O indice `tau` aqui e o tempo aritmetico inteiro da torre prima nativa. Este
arquivo **nao** identifica essa torre/esse tempo com uma camera Green nem com a
altura espectral do operador Genuine. Portanto, os resultados abaixo sao uma
peca Bessel verdadeira para `G_pre`, mas nao constituem por si mesmos a ponte
de observabilidade do Genuine.
-/

open scoped BigOperators

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Para tempo aritmetico positivo, as normas quadradas das torres nativas sao
somaveis sobre todas as bases primas. -/
theorem summable_nativeGpreTowerProfileVector_norm_sq_over_primes
    (tau : ℕ) (htau : 1 ≤ tau) :
    Summable (fun p : Nat.Primes =>
      ‖nativeGpreTowerProfileVector (p : ℕ) tau‖ ^ 2) := by
  have hnat : Summable (fun n : ℕ => ((n : ℝ) ^ (2 * tau))⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by omega)
  let primeToNat : Nat.Primes → ℕ := fun p => (p : ℕ)
  have hinjective : Function.Injective primeToNat := by
    intro p q hpq
    exact Nat.Primes.coe_nat_injective hpq
  have hprime := hnat.comp_injective hinjective
  have hmajorant := hprime.mul_left (4 / 3 : ℝ)
  exact Summable.of_nonneg_of_le
    (fun p => sq_nonneg ‖nativeGpreTowerProfileVector (p : ℕ) tau‖)
    (fun p => by
      exact nativeGpreTowerProfileVector_norm_sq_le_of_pos
        (p : ℕ) tau p.property.two_le htau)
    hmajorant

end

end CPFormal.Analytic.Cp
