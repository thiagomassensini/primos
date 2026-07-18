import CPFormal.Genuine.BalancedOffsets

/-!
# Residuos nao nulos e offsets balanceados Cp

Para um primo impar `p`, cada residuo nao nulo modulo `p` possui um unico
representante no intervalo balanceado

`[-(p-1)/2, (p-1)/2] \ {0}`.

Usamos `ZMod.valMinAbs` como representante canonico. Este e o passo finito que
identifica as `p-1` pernas da camera Cp com os residuos nao nulos.

Nao ha serie, limite, zeta ou zero analitico neste arquivo.
-/

namespace CPFormal.Carry.Cp

open CPFormal.Genuine.Cp

/-- Um offset que pertence a camera balanceada de base `p`. -/
def BalancedOffset (p : ℕ) :=
  {a : ℤ // a ∈ balancedOffsets p}

/-- Um residuo nao nulo modulo `p`. -/
def NonzeroResidue (p : ℕ) :=
  {x : ZMod p // x ≠ 0}

/-- Para `p` impar, o semialcance tambem e `p/2`. -/
theorem halfRange_eq_div_two {p : ℕ} (hpodd : Odd p) :
    halfRange p = p / 2 := by
  rcases hpodd with ⟨q, hq⟩
  unfold halfRange
  omega

/-- Forma aritmetica de um modulo impar em torno de seu semialcance. -/
theorem two_mul_halfRange_add_one {p : ℕ} (hpodd : Odd p) :
    2 * halfRange p + 1 = p := by
  rcases hpodd with ⟨q, hq⟩
  unfold halfRange
  omega

/--
O representante minimo de um offset que ja esta na camera e o proprio offset.
-/
theorem valMinAbs_intCast_of_mem
    {p : ℕ} (hp : Nat.Prime p) (hpodd : Odd p)
    {a : ℤ} (ha : a ∈ balancedOffsets p) :
    (a : ZMod p).valMinAbs = a := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hpformNat := two_mul_halfRange_add_one hpodd
  have hpformInt :
      (p : ℤ) = 2 * (halfRange p : ℤ) + 1 := by
    exact_mod_cast hpformNat.symm
  have habounds := (mem_balancedOffsets_iff.mp ha).2
  apply (ZMod.valMinAbs_spec (a : ZMod p) a).2
  refine ⟨rfl, ?_⟩
  constructor <;> omega

/-- Converter um offset balanceado produz um residuo nao nulo. -/
def residueOfBalanced
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) :
    BalancedOffset p → NonzeroResidue p := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro a
  refine ⟨(a.1 : ZMod p), ?_⟩
  intro hzero
  have ha0 : a.1 = 0 := by
    calc
      a.1 = (a.1 : ZMod p).valMinAbs :=
        (valMinAbs_intCast_of_mem hp hpodd a.2).symm
      _ = (0 : ZMod p).valMinAbs :=
        congrArg (fun x : ZMod p => x.valMinAbs) hzero
      _ = 0 := ZMod.valMinAbs_zero p
  exact (mem_balancedOffsets_iff.mp a.2).1 ha0

/-- O representante minimo de um residuo nao nulo pertence a camera. -/
def balancedOfResidue
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) :
    NonzeroResidue p → BalancedOffset p := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro x
  refine ⟨x.1.valMinAbs, ?_⟩
  apply mem_balancedOffsets_iff.mpr
  constructor
  · intro hzero
    exact x.2 ((ZMod.valMinAbs_eq_zero x.1).mp hzero)
  · have hpformNat := two_mul_halfRange_add_one hpodd
    have hpformInt :
        (p : ℤ) = 2 * (halfRange p : ℤ) + 1 := by
      exact_mod_cast hpformNat.symm
    have hwindow := ZMod.valMinAbs_mem_Ioc x.1
    constructor <;> omega

/--
Bijeção canonica entre as pernas balanceadas e os residuos nao nulos modulo
um primo impar.
-/
noncomputable def balancedOffsetEquivNonzeroResidue
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) :
    BalancedOffset p ≃ NonzeroResidue p where
  toFun := residueOfBalanced p hp hpodd
  invFun := balancedOfResidue p hp hpodd
  left_inv a := by
    apply Subtype.ext
    change (a.1 : ZMod p).valMinAbs = a.1
    exact valMinAbs_intCast_of_mem hp hpodd a.2
  right_inv x := by
    apply Subtype.ext
    change ((x.1.valMinAbs : ℤ) : ZMod p) = x.1
    exact ZMod.coe_valMinAbs x.1

/-- A camera balanceada de modulo impar possui exatamente `p-1` pernas. -/
theorem card_balancedOffsets {p : ℕ} (hpodd : Odd p) :
    (balancedOffsets p).card = p - 1 := by
  have hpformNat := two_mul_halfRange_add_one hpodd
  have hpformInt :
      (p : ℤ) = 2 * (halfRange p : ℤ) + 1 := by
    exact_mod_cast hpformNat.symm
  have hcard :
      (Finset.Icc (-(halfRange p : ℤ)) (halfRange p : ℤ)).card = p := by
    rw [Int.card_Icc]
    rw [show
      (halfRange p : ℤ) + 1 - (-(halfRange p : ℤ)) = (p : ℤ) by omega]
    simp
  unfold balancedOffsets
  rw [Finset.card_erase_of_mem]
  · rw [hcard]
  · simp

end CPFormal.Carry.Cp
