import CPFormal.Carry.C2Adjacent
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Profundidade efetiva do carry C2

Este arquivo liga a definicao do documento

`k_eff(n) = max (v_2(n-1)) (v_2(n+1))`

ao centro combinatorio escolhido em `C2Adjacent`. Para um impar `n >= 3`, um
dos vizinhos e congruente a `2 mod 4` e tem profundidade exatamente `1`; o
outro e o centro multiplo de quatro e tem profundidade pelo menos `2`.
-/

namespace CPFormal.Carry.C2

/-- Profundidade efetiva apresentada pelo canal direto C2. -/
def effectiveDepth (n : ℕ) : ℕ :=
  max (padicValNat 2 (n - 1)) (padicValNat 2 (n + 1))

/-- Um natural congruente a `2 mod 4` possui profundidade 2-adica exatamente `1`. -/
theorem padicValNat_two_eq_one_of_mod_four_two {m : ℕ} (hm : m % 4 = 2) :
    padicValNat 2 m = 1 := by
  have hm0 : m ≠ 0 := by omega
  have htwo : 2 ∣ m := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  have hfour : ¬4 ∣ m := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  have hlo : 1 ≤ padicValNat 2 m :=
    one_le_padicValNat_of_dvd hm0 htwo
  have hhi : ¬2 ≤ padicValNat 2 m := by
    intro hdepth
    have hpow : 2 ^ 2 ∣ m :=
      (padicValNat_dvd_iff_le (p := 2) hm0).2 hdepth
    norm_num at hpow
    exact hfour hpow
  omega

/-- O centro C2 escolhido possui profundidade 2-adica pelo menos `2`. -/
theorem two_le_centerDepth {n : ℕ} (hn3 : 3 ≤ n) (hn : Odd n) :
    2 ≤ padicValNat 2 (adjacentCenter n) := by
  have hc4 := four_le_adjacentCenter hn3 hn
  have hc0 : adjacentCenter n ≠ 0 := by omega
  apply (padicValNat_dvd_iff_le (p := 2) hc0).1
  norm_num
  exact four_dvd_adjacentCenter hn

/--
Ponte peso--carry C2: a profundidade efetiva da perna e exatamente a
profundidade 2-adica do seu centro unico.
-/
theorem effectiveDepth_eq_centerDepth {n : ℕ} (hn3 : 3 ≤ n) (hn : Odd n) :
    effectiveDepth n = padicValNat 2 (adjacentCenter n) := by
  have hcenter := two_le_centerDepth hn3 hn
  rcases odd_mod_four hn with h | h
  · have hotherMod : (n + 1) % 4 = 2 := by omega
    have hother := padicValNat_two_eq_one_of_mod_four_two hotherMod
    rw [adjacentCenter_of_mod_one h] at hcenter
    rw [effectiveDepth, adjacentCenter_of_mod_one h]
    rw [hother, max_eq_left (by omega)]
  · have hotherMod : (n - 1) % 4 = 2 := by omega
    have hother := padicValNat_two_eq_one_of_mod_four_two hotherMod
    rw [adjacentCenter_of_mod_three h] at hcenter
    rw [effectiveDepth, adjacentCenter_of_mod_three h]
    rw [hother, max_eq_right (by omega)]

end CPFormal.Carry.C2
