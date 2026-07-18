import CPFormal.Carry.CpBalancedResidue

/-!
# Bijeção global centro--offset Cₚ

Fixe um primo ímpar `p`. Todo inteiro `n` não divisível por `p` admite uma
decomposição única

`n = c + a`,

na qual `p ∣ c` e `a` é um offset balanceado não nulo da câmera Cₚ. O offset
é o representante `ZMod.valMinAbs` da classe residual de `n`; o centro é
literalmente `n - a`.

Este arquivo prova a bijeção global entre pernas e incidências
`(centro múltiplo de p, offset balanceado)`. Não há série, limite, zeta ou
afirmação espectral aqui.
-/

namespace CPFormal.Carry.Cp

open CPFormal.Genuine.Cp

noncomputable section

/-- Inteiros que não pertencem à vertical de base `p`. -/
def Nonmultiple (p : ℕ) :=
  {n : ℤ // ¬(p : ℤ) ∣ n}

/--
Uma incidência Cₚ guarda um centro múltiplo de `p` e um offset balanceado.
A perna correspondente é recuperada somando as duas coordenadas.
-/
def Incidence (p : ℕ) :=
  {x : ℤ × BalancedOffset p // (p : ℤ) ∣ x.1}

/-- A classe residual não nula de uma perna Cₚ. -/
def residueOfNonmultiple (p : ℕ) (n : Nonmultiple p) : NonzeroResidue p := by
  refine ⟨(n.1 : ZMod p), ?_⟩
  intro hzero
  exact n.2 ((ZMod.intCast_zmod_eq_zero_iff_dvd n.1 p).mp hzero)

/-- O único offset balanceado congruente à perna módulo `p`. -/
def offsetOfNonmultiple
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (n : Nonmultiple p) : BalancedOffset p :=
  (balancedOffsetEquivNonzeroResidue p hp hpodd).symm
    (residueOfNonmultiple p n)

/-- O offset escolhido representa exatamente a classe residual da perna. -/
@[simp] theorem cast_offsetOfNonmultiple
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (n : Nonmultiple p) :
    ((offsetOfNonmultiple p hp hpodd n).1 : ZMod p) = (n.1 : ZMod p) := by
  simpa [offsetOfNonmultiple] using congrArg Subtype.val
    ((balancedOffsetEquivNonzeroResidue p hp hpodd).apply_symm_apply
      (residueOfNonmultiple p n))

/-- O centro canônico é o que sobra depois de retirar o offset balanceado. -/
def centerOfNonmultiple
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (n : Nonmultiple p) : ℤ :=
  n.1 - (offsetOfNonmultiple p hp hpodd n).1

/-- O centro canônico pertence à vertical de base `p`. -/
theorem dvd_centerOfNonmultiple
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (n : Nonmultiple p) :
    (p : ℤ) ∣ centerOfNonmultiple p hp hpodd n := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd
    (centerOfNonmultiple p hp hpodd n) p).mp
  change (n.1 : ZMod p) -
    ((offsetOfNonmultiple p hp hpodd n).1 : ZMod p) = 0
  rw [cast_offsetOfNonmultiple]
  simp

/-- A incidência determinada por uma perna não múltipla de `p`. -/
def incidenceOfNonmultiple
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (n : Nonmultiple p) : Incidence p :=
  ⟨(centerOfNonmultiple p hp hpodd n,
      offsetOfNonmultiple p hp hpodd n),
    dvd_centerOfNonmultiple p hp hpodd n⟩

/-- A perna guardada por uma incidência continua não divisível por `p`. -/
def nonmultipleOfIncidence
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (x : Incidence p) : Nonmultiple p := by
  refine ⟨x.1.1 + x.1.2.1, ?_⟩
  intro hdiv
  have hsum : ((x.1.1 + x.1.2.1 : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd
      (x.1.1 + x.1.2.1) p).mpr hdiv
  have hcenter : (x.1.1 : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd x.1.1 p).mpr x.2
  have hoffset : (x.1.2.1 : ZMod p) = 0 := by
    simpa [hcenter] using hsum
  exact (residueOfBalanced p hp hpodd x.1.2).2 hoffset

/-- Retirar o offset e recolocá-lo recupera literalmente a perna. -/
@[simp] theorem incidenceOfNonmultiple_leg
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (n : Nonmultiple p) :
    (incidenceOfNonmultiple p hp hpodd n).1.1 +
      (incidenceOfNonmultiple p hp hpodd n).1.2.1 = n.1 := by
  simp [incidenceOfNonmultiple, centerOfNonmultiple]

/--
Começar por uma incidência e recalcular o representante balanceado preserva
exatamente o offset original.
-/
theorem offsetOf_nonmultipleOfIncidence
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (x : Incidence p) :
    offsetOfNonmultiple p hp hpodd
      (nonmultipleOfIncidence p hp hpodd x) = x.1.2 := by
  let e := balancedOffsetEquivNonzeroResidue p hp hpodd
  change e.symm
    (residueOfNonmultiple p (nonmultipleOfIncidence p hp hpodd x)) = x.1.2
  apply e.injective
  rw [e.apply_symm_apply]
  apply Subtype.ext
  change ((x.1.1 + x.1.2.1 : ℤ) : ZMod p) = (x.1.2.1 : ZMod p)
  have hcenter : (x.1.1 : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd x.1.1 p).mpr x.2
  simp [hcenter]

/--
Bijeção global Cₚ: pernas não múltiplas de `p` correspondem exatamente às
incidências `(centro múltiplo de p, offset balanceado)`.
-/
noncomputable def nonmultipleEquivIncidence
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) :
    Nonmultiple p ≃ Incidence p where
  toFun := incidenceOfNonmultiple p hp hpodd
  invFun := nonmultipleOfIncidence p hp hpodd
  left_inv n := by
    apply Subtype.ext
    exact incidenceOfNonmultiple_leg p hp hpodd n
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · change centerOfNonmultiple p hp hpodd
        (nonmultipleOfIncidence p hp hpodd x) = x.1.1
      unfold centerOfNonmultiple
      rw [congrArg Subtype.val
        (offsetOf_nonmultipleOfIncidence p hp hpodd x)]
      change (x.1.1 + x.1.2.1) - x.1.2.1 = x.1.1
      ring
    · exact offsetOf_nonmultipleOfIncidence p hp hpodd x

/--
Forma existencial e única da decomposição: para cada perna há exatamente uma
incidência cujo centro mais offset é essa perna.
-/
theorem existsUnique_incidence
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (n : Nonmultiple p) :
    ∃! x : Incidence p, x.1.1 + x.1.2.1 = n.1 := by
  let e := nonmultipleEquivIncidence p hp hpodd
  refine ⟨e n, ?_, ?_⟩
  · exact incidenceOfNonmultiple_leg p hp hpodd n
  · intro x hx
    have hinv : e.symm x = n := by
      apply Subtype.ext
      change x.1.1 + x.1.2.1 = n.1
      exact hx
    calc
      x = e (e.symm x) := (e.apply_symm_apply x).symm
      _ = e n := congrArg e hinv

end

end CPFormal.Carry.Cp
