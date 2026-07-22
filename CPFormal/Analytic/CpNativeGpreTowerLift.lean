import CPFormal.Analytic.CpGpreTypes
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Lift aritmetico nativo `G_pre`

Este modulo inicia o checkpoint 0.51 construindo as coordenadas aritmeticas
que, no checkpoint anterior, apareciam apenas pela interface abstrata
`NativeGpreTowerLiftCertificate`.

A primeira camada e puramente algebraica. O divisor de Jordan `d_J`, o tempo
aritmetico `tau`, o primo da camera e o nivel material da torre permanecem
indices distintos. A soma em `d_J | gcd(u,v)` e provada pelo kernel mediante
inversao de Moebius; ela recupera o readout reduzido do par antes de qualquer
norma, cutoff, parametro espectral ou hipotese de zero Genuine.
-/

open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius

namespace CPFormal.Analytic.Cp

noncomputable section

open ArithmeticFunction

/-!
## Fibras Mobius--Jordan
-/

/-- Perfil aritmetico `n |-> n^(2*tau)` como funcao aritmetica inteira. -/
def nativeGprePowerArithmetic (tau : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n = 0 then 0 else (n : ℤ) ^ (2 * tau), by simp⟩

@[simp] theorem nativeGprePowerArithmetic_zero (tau : ℕ) :
    nativeGprePowerArithmetic tau 0 = 0 := rfl

@[simp] theorem nativeGprePowerArithmetic_apply
    (tau n : ℕ) (hn : n ≠ 0) :
    nativeGprePowerArithmetic tau n = (n : ℤ) ^ (2 * tau) := by
  simp [nativeGprePowerArithmetic, hn]

/-- Perfil de valuacao `v_p(n) n^(2*tau)` antes da inversao de Moebius. -/
def nativeGpreValuationPowerArithmetic
    (p tau : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n =>
      if n = 0 then 0
      else (Nat.factorization n p : ℤ) * (n : ℤ) ^ (2 * tau),
    by simp⟩

@[simp] theorem nativeGpreValuationPowerArithmetic_zero (p tau : ℕ) :
    nativeGpreValuationPowerArithmetic p tau 0 = 0 := rfl

@[simp] theorem nativeGpreValuationPowerArithmetic_apply
    (p tau n : ℕ) (hn : n ≠ 0) :
    nativeGpreValuationPowerArithmetic p tau n =
      (Nat.factorization n p : ℤ) * (n : ℤ) ^ (2 * tau) := by
  simp [nativeGpreValuationPowerArithmetic, hn]

/-- Canal de Jordan `J_(2*tau) = mu * power_(2*tau)`. -/
def nativeGpreJordanArithmetic (tau : ℕ) : ArithmeticFunction ℤ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℤ) *
    nativeGprePowerArithmetic tau

/-- Canal logaritmico `H_(p,tau) = mu * (v_p * power_(2*tau))`. -/
def nativeGpreHArithmetic (p tau : ℕ) : ArithmeticFunction ℤ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℤ) *
    nativeGpreValuationPowerArithmetic p tau

/-- Somar o canal Jordan em todos os divisores desfaz literalmente a
inversao de Moebius. -/
theorem sum_divisors_nativeGpreJordanArithmetic
    (tau ell : ℕ) (hell : ell ≠ 0) :
    (∑ d ∈ ell.divisors, nativeGpreJordanArithmetic tau d) =
      (ell : ℤ) ^ (2 * tau) := by
  rw [← ArithmeticFunction.coe_zeta_mul_apply]
  change (((ArithmeticFunction.zeta : ArithmeticFunction ℤ) *
      ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) *
        nativeGprePowerArithmetic tau)) ell) = _
  rw [← mul_assoc, ArithmeticFunction.coe_zeta_mul_moebius, one_mul]
  exact nativeGprePowerArithmetic_apply tau ell hell

/-- A mesma inversao no canal logaritmico recupera
`v_p(ell) ell^(2*tau)`. -/
theorem sum_divisors_nativeGpreHArithmetic
    (p tau ell : ℕ) (hell : ell ≠ 0) :
    (∑ d ∈ ell.divisors, nativeGpreHArithmetic p tau d) =
      (Nat.factorization ell p : ℤ) * (ell : ℤ) ^ (2 * tau) := by
  rw [← ArithmeticFunction.coe_zeta_mul_apply]
  change (((ArithmeticFunction.zeta : ArithmeticFunction ℤ) *
      ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) *
        nativeGpreValuationPowerArithmetic p tau)) ell) = _
  rw [← mul_assoc, ArithmeticFunction.coe_zeta_mul_moebius, one_mul]
  exact nativeGpreValuationPowerArithmetic_apply p tau ell hell

/-!
## Coordenada divisor-resolvida
-/

/-- Soma das duas valuacoes que entram num canto `(u,v)`. -/
def nativeGprePairValuation (u v p : ℕ) : ℤ :=
  (Nat.factorization u p : ℤ) + (Nat.factorization v p : ℤ)

/-- Numerador inteiro da coordenada historica
`J_(2*tau)(d) a_p - 2 H_(p,tau)(d)`. -/
def nativeGpreJordanBracket
    (u v p tau d : ℕ) : ℤ :=
  nativeGpreJordanArithmetic tau d * nativeGprePairValuation u v p -
    2 * nativeGpreHArithmetic p tau d

/-- A soma completa no divisor de Jordan e fechada antes de introduzir o
denominador `(uv)^tau`. -/
theorem sum_divisors_nativeGpreJordanBracket
    (u v p tau ell : ℕ) (hell : ell ≠ 0) :
    (∑ d ∈ ell.divisors, nativeGpreJordanBracket u v p tau d) =
      (ell : ℤ) ^ (2 * tau) *
        (nativeGprePairValuation u v p -
          2 * (Nat.factorization ell p : ℤ)) := by
  unfold nativeGpreJordanBracket
  rw [Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  rw [← Finset.mul_sum]
  rw [sum_divisors_nativeGpreJordanArithmetic tau ell hell]
  rw [sum_divisors_nativeGpreHArithmetic p tau ell hell]
  ring

/-- Coordenada racional de `G_pre/log(p)` num divisor de Jordan. O sinal
`b_uv` e mantido como inteiro para preservar exatamente os quatro cantos. -/
def nativeGpreDivisorCoordinate
    (sign : ℤ) (u v p tau d : ℕ) : ℚ :=
  ((sign * nativeGpreJordanBracket u v p tau d : ℤ) : ℚ) /
    ((u * v : ℕ) : ℚ) ^ tau

/-- Readout fechado obtido depois de somar o eixo `d_J`. -/
def nativeGpreClosedDivisorReadout
    (sign : ℤ) (u v p tau ell : ℕ) : ℚ :=
  ((sign *
      ((ell : ℤ) ^ (2 * tau) *
        (nativeGprePairValuation u v p -
          2 * (Nat.factorization ell p : ℤ))) : ℤ) : ℚ) /
    ((u * v : ℕ) : ℚ) ^ tau

/-- Fatoracao exata da fibra divisor-resolvida. Este e o teorema geral que
substitui os 675 witnesses finitos do preflight. -/
theorem sum_divisors_nativeGpreDivisorCoordinate
    (sign : ℤ) (u v p tau ell : ℕ) (hell : ell ≠ 0) :
    (∑ d ∈ ell.divisors,
        nativeGpreDivisorCoordinate sign u v p tau d) =
      nativeGpreClosedDivisorReadout sign u v p tau ell := by
  unfold nativeGpreDivisorCoordinate nativeGpreClosedDivisorReadout
  rw [← Finset.sum_div]
  simp only [Int.cast_mul]
  rw [← Finset.mul_sum]
  rw [← Int.cast_sum]
  rw [sum_divisors_nativeGpreJordanBracket u v p tau ell hell]
  norm_cast

/-!
## Readout no par reduzido
-/

/-- Valuacao do par depois de remover o gcd comum. -/
def nativeGpreReducedPairValuation (u v p : ℕ) : ℤ :=
  (Nat.factorization (u / Nat.gcd u v) p : ℤ) +
    (Nat.factorization (v / Nat.gcd u v) p : ℤ)

/-- O termo `a_p - 2 v_p(gcd(u,v))` e literalmente a valuacao do par
reduzido. Nenhuma primalidade de `p` e necessaria para esta identidade. -/
theorem nativeGprePairValuation_sub_two_gcd_eq_reduced
    (u v p : ℕ) (hu : u ≠ 0) (hv : v ≠ 0) :
    nativeGprePairValuation u v p -
        2 * (Nat.factorization (Nat.gcd u v) p : ℤ) =
      nativeGpreReducedPairValuation u v p := by
  let ell := Nat.gcd u v
  have hell : ell ≠ 0 :=
    (Nat.gcd_pos_of_pos_left v (Nat.pos_of_ne_zero hu)).ne'
  have hleuF : ell.factorization ≤ u.factorization :=
    (Nat.factorization_le_iff_dvd hell hu).2 (Nat.gcd_dvd_left u v)
  have hlevF : ell.factorization ≤ v.factorization :=
    (Nat.factorization_le_iff_dvd hell hv).2 (Nat.gcd_dvd_right u v)
  have hleu : ell.factorization p ≤ u.factorization p := hleuF p
  have hlev : ell.factorization p ≤ v.factorization p := hlevF p
  have hdivu :
      (u / ell).factorization p =
        u.factorization p - ell.factorization p := by
    simpa [ell] using congrArg (fun f : ℕ →₀ ℕ => f p)
      (Nat.factorization_div (Nat.gcd_dvd_left u v))
  have hdivv :
      (v / ell).factorization p =
        v.factorization p - ell.factorization p := by
    simpa [ell] using congrArg (fun f : ℕ →₀ ℕ => f p)
      (Nat.factorization_div (Nat.gcd_dvd_right u v))
  have hcastu :
      (u.factorization p : ℤ) - (ell.factorization p : ℤ) =
        ((u / ell).factorization p : ℤ) := by
    rw [← Nat.cast_sub hleu]
    exact_mod_cast hdivu.symm
  have hcastv :
      (v.factorization p : ℤ) - (ell.factorization p : ℤ) =
        ((v / ell).factorization p : ℤ) := by
    rw [← Nat.cast_sub hlev]
    exact_mod_cast hdivv.symm
  unfold nativeGprePairValuation nativeGpreReducedPairValuation
  change
    (u.factorization p : ℤ) + (v.factorization p : ℤ) -
        2 * (ell.factorization p : ℤ) =
      ((u / ell).factorization p : ℤ) +
        ((v / ell).factorization p : ℤ)
  linarith

/-- Readout de `G_pre/log(p)` escrito diretamente no par reduzido, ainda com
o fator de escala comum visivel. -/
def nativeGpreReducedPairReadout
    (sign : ℤ) (u v p tau : ℕ) : ℚ :=
  let ell := Nat.gcd u v
  ((sign *
      ((ell : ℤ) ^ (2 * tau) *
        nativeGpreReducedPairValuation u v p) : ℤ) : ℚ) /
    ((u * v : ℕ) : ℚ) ^ tau

/-- Especializar o readout fechado em `ell=gcd(u,v)` produz exatamente o
readout do par reduzido. -/
theorem nativeGpreClosedDivisorReadout_gcd_eq_reduced
    (sign : ℤ) (u v p tau : ℕ) (hu : u ≠ 0) (hv : v ≠ 0) :
    nativeGpreClosedDivisorReadout sign u v p tau (Nat.gcd u v) =
      nativeGpreReducedPairReadout sign u v p tau := by
  unfold nativeGpreClosedDivisorReadout nativeGpreReducedPairReadout
  rw [nativeGprePairValuation_sub_two_gcd_eq_reduced u v p hu hv]

/-- Fatoracao completa da fibra nativa: a soma em todos os divisores Jordan
do gcd recupera o readout do par reduzido. -/
theorem sum_gcdDivisors_nativeGpreDivisorCoordinate_eq_reduced
    (sign : ℤ) (u v p tau : ℕ) (hu : u ≠ 0) (hv : v ≠ 0) :
    (∑ d ∈ (Nat.gcd u v).divisors,
        nativeGpreDivisorCoordinate sign u v p tau d) =
      nativeGpreReducedPairReadout sign u v p tau := by
  rw [sum_divisors_nativeGpreDivisorCoordinate sign u v p tau
      (Nat.gcd u v)
      ((Nat.gcd_pos_of_pos_left v (Nat.pos_of_ne_zero hu)).ne')]
  exact nativeGpreClosedDivisorReadout_gcd_eq_reduced
    sign u v p tau hu hv

/-!
## Os quatro cantos nativos da aresta C2
-/

/-- Vertice vertical `u` do canto de uma aresta positiva `e`. -/
def nativeGpreCornerU (e : ℕ) : GpreCorner → ℕ
  | .lowerLeft => 2 * e
  | .lowerRight => 2 * e
  | .upperLeft => 2 * e + 2
  | .upperRight => 2 * e + 2

/-- Vertice horizontal `v` do mesmo canto. -/
def nativeGpreCornerV (e : ℕ) : GpreCorner → ℕ
  | .lowerLeft => e
  | .lowerRight => e + 1
  | .upperLeft => e
  | .upperRight => e + 1

/-- Orientacao assinada `(+1,-1,-1,+1)` da celula C2. -/
def nativeGpreCornerSign : GpreCorner → ℤ
  | .lowerLeft => 1
  | .lowerRight => -1
  | .upperLeft => -1
  | .upperRight => 1

theorem nativeGpreCornerU_ne_zero
    (e : ℕ) (he : e ≠ 0) (corner : GpreCorner) :
    nativeGpreCornerU e corner ≠ 0 := by
  cases corner <;> simp [nativeGpreCornerU, he]

theorem nativeGpreCornerV_ne_zero
    (e : ℕ) (he : e ≠ 0) (corner : GpreCorner) :
    nativeGpreCornerV e corner ≠ 0 := by
  cases corner <;> simp [nativeGpreCornerV, he]

/-- Coordenada literal do canto nativo em `(p,tau,d_J)`. -/
def nativeGpreCornerDivisorCoordinate
    (e : ℕ) (corner : GpreCorner) (p tau d : ℕ) : ℚ :=
  nativeGpreDivisorCoordinate
    (nativeGpreCornerSign corner)
    (nativeGpreCornerU e corner)
    (nativeGpreCornerV e corner)
    p tau d

/-- Readout reduzido do mesmo canto depois de esquecer apenas `d_J`. -/
def nativeGpreCornerReducedReadout
    (e : ℕ) (corner : GpreCorner) (p tau : ℕ) : ℚ :=
  nativeGpreReducedPairReadout
    (nativeGpreCornerSign corner)
    (nativeGpreCornerU e corner)
    (nativeGpreCornerV e corner)
    p tau

/-- A fatoracao `Q G_pre = readout` vale canto por canto em toda aresta
positiva, com o mesmo tipo de canto usado pelo carrier de `Qtilde`. -/
theorem sum_gcdDivisors_nativeGpreCornerCoordinate_eq_readout
    (e : ℕ) (he : e ≠ 0) (corner : GpreCorner) (p tau : ℕ) :
    (∑ d ∈
        (Nat.gcd (nativeGpreCornerU e corner)
          (nativeGpreCornerV e corner)).divisors,
      nativeGpreCornerDivisorCoordinate e corner p tau d) =
        nativeGpreCornerReducedReadout e corner p tau := by
  exact sum_gcdDivisors_nativeGpreDivisorCoordinate_eq_reduced
    (nativeGpreCornerSign corner)
    (nativeGpreCornerU e corner)
    (nativeGpreCornerV e corner)
    p tau
    (nativeGpreCornerU_ne_zero e he corner)
    (nativeGpreCornerV_ne_zero e he corner)

/-!
## Lift coordenado com a torre material preservada
-/

/-- Fator da completacao reciproca assinada. A orientacao original conserva
o coeficiente; a reciproca aplica `-(v/u)`, exatamente como o involutor
ponderado `Theta[u,v]=(v/u)[v,u]`. -/
noncomputable def nativeGpreOrientationFactor
    (e : ℕ) (corner : GpreCorner) : GpreOrientation → ℝ
  | .original => 1
  | .reciprocal =>
      -((nativeGpreCornerV e corner : ℝ) /
        (nativeGpreCornerU e corner : ℝ))

/-- O componente de fluxo recebe a acao do operador numero `j`. -/
def nativeGpreGraphRoleFactor (j : ℕ) : GpreGraphRole → ℝ
  | .value => 1
  | .numberFlux => j

/-- Coeficiente completo de uma coordenada tipada do lift aritmetico antes
do dressing espectral TFVD. Coordenadas fora do suporte nativo sao zero. -/
noncomputable def nativeGpreTowerCoordinateCoefficient
    (c : NativeGpreContext) : ℝ :=
  if c.cell = 0 then 0
  else if c.towerPrime.val = c.arithmeticPrime.val then
    let u := nativeGpreCornerU c.cell c.corner
    let v := nativeGpreCornerV c.cell c.corner
    if c.jordanDivisor.val ∣ Nat.gcd u v then
      (nativeGpreCornerDivisorCoordinate
          c.cell c.corner c.arithmeticPrime.val c.time.val
          c.jordanDivisor.val : ℝ) *
        Real.log c.arithmeticPrime.val *
        nativeUnitMassTowerProfile
          c.towerPrime.val c.time.val c.towerLevel.val *
        nativeGpreOrientationFactor c.cell c.corner c.orientation *
        nativeGpreGraphRoleFactor c.towerLevel.val c.role
    else 0
  else 0

@[simp] theorem nativeGpreTowerCoordinateCoefficient_zero_cell
    (c : NativeGpreContext) (hcell : c.cell = 0) :
    nativeGpreTowerCoordinateCoefficient c = 0 := by
  simp [nativeGpreTowerCoordinateCoefficient, hcell]

@[simp] theorem nativeGpreTowerCoordinateCoefficient_tower_mismatch
    (c : NativeGpreContext)
    (htower : c.towerPrime.val ≠ c.arithmeticPrime.val) :
    nativeGpreTowerCoordinateCoefficient c = 0 := by
  by_cases hcell : c.cell = 0
  · simp [nativeGpreTowerCoordinateCoefficient, hcell]
  · simp [nativeGpreTowerCoordinateCoefficient, hcell, htower]

/-- Core algebrico das arestas. O indice zero permanece disponivel no tipo,
mas todas as coordenadas nativas sobre ele sao anuladas pelo suporte. -/
abbrev NativeGpreEdgeCore := ℕ →₀ ℝ

/-- Carrier coordenado anterior a prova de somabilidade `l2`. -/
abbrev NativeGpreCoordinateCarrier := NativeGpreContext → ℝ

/-- Lift aritmetico nativo literal. Cada contexto preserva sua aresta, canto,
primo, tempo, divisor Jordan, orientacao, perna, papel e nivel de torre. -/
noncomputable def nativeGpreTowerLiftLinearMap :
    NativeGpreEdgeCore →ₗ[ℝ] NativeGpreCoordinateCarrier where
  toFun x c := x c.cell * nativeGpreTowerCoordinateCoefficient c
  map_add' x y := by
    funext c
    simp [add_mul]
  map_smul' a x := by
    funext c
    simp [mul_assoc]

@[simp] theorem nativeGpreTowerLiftLinearMap_apply
    (x : NativeGpreEdgeCore) (c : NativeGpreContext) :
    nativeGpreTowerLiftLinearMap x c =
      x c.cell * nativeGpreTowerCoordinateCoefficient c := rfl

@[simp] theorem nativeGpreTowerLiftLinearMap_single_apply
    (e : ℕ) (a : ℝ) (c : NativeGpreContext) :
    nativeGpreTowerLiftLinearMap (Finsupp.single e a) c =
      if e = c.cell then
        a * nativeGpreTowerCoordinateCoefficient c
      else 0 := by
  classical
  by_cases h : e = c.cell
  · subst e
    simp [nativeGpreTowerLiftLinearMap_apply]
  · have h' : c.cell ≠ e := Ne.symm h
    simp [nativeGpreTowerLiftLinearMap_apply, h, h']

/-- Troca somente o divisor Jordan, preservando literalmente todos os outros
eixos do contexto. -/
def nativeGpreContextWithDivisor
    (c : NativeGpreContext) (d : ℕ) : NativeGpreContext :=
  { c with jordanDivisor := ⟨d⟩ }

/-- Fator externo a soma em `d_J`: camera logaritmica, perfil material da
torre, orientacao assinada e papel valor--fluxo. -/
noncomputable def nativeGpreTowerOuterFactor
    (c : NativeGpreContext) : ℝ :=
  Real.log c.arithmeticPrime.val *
    nativeUnitMassTowerProfile
      c.towerPrime.val c.time.val c.towerLevel.val *
    nativeGpreOrientationFactor c.cell c.corner c.orientation *
    nativeGpreGraphRoleFactor c.towerLevel.val c.role

/-- O readout `Q` da fibra completa de divisores coincide com o readout
reduzido do canto, agora ja tensorizado com a torre material. -/
theorem sum_gcdDivisors_nativeGpreTowerCoordinate_eq_readout
    (c : NativeGpreContext)
    (hcell : c.cell ≠ 0)
    (htower : c.towerPrime.val = c.arithmeticPrime.val) :
    (∑ d ∈
        (Nat.gcd (nativeGpreCornerU c.cell c.corner)
          (nativeGpreCornerV c.cell c.corner)).divisors,
      nativeGpreTowerCoordinateCoefficient
        (nativeGpreContextWithDivisor c d)) =
      (nativeGpreCornerReducedReadout
          c.cell c.corner c.arithmeticPrime.val c.time.val : ℝ) *
        nativeGpreTowerOuterFactor c := by
  let divisorSet :=
    (Nat.gcd (nativeGpreCornerU c.cell c.corner)
      (nativeGpreCornerV c.cell c.corner)).divisors
  let outer := nativeGpreTowerOuterFactor c
  have hsumQ :=
    sum_gcdDivisors_nativeGpreCornerCoordinate_eq_readout
      c.cell hcell c.corner c.arithmeticPrime.val c.time.val
  have hsumR :
      (∑ d ∈ divisorSet,
          (nativeGpreCornerDivisorCoordinate
            c.cell c.corner c.arithmeticPrime.val c.time.val d : ℝ)) =
        (nativeGpreCornerReducedReadout
          c.cell c.corner c.arithmeticPrime.val c.time.val : ℝ) := by
    exact_mod_cast hsumQ
  calc
    (∑ d ∈ divisorSet,
        nativeGpreTowerCoordinateCoefficient
          (nativeGpreContextWithDivisor c d)) =
        ∑ d ∈ divisorSet,
          (nativeGpreCornerDivisorCoordinate
            c.cell c.corner c.arithmeticPrime.val c.time.val d : ℝ) *
              outer := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdvd :
          d ∣ Nat.gcd (nativeGpreCornerU c.cell c.corner)
            (nativeGpreCornerV c.cell c.corner) :=
        Nat.dvd_of_mem_divisors hd
      simp [nativeGpreTowerCoordinateCoefficient,
        nativeGpreContextWithDivisor, hcell, htower, hdvd,
        outer, nativeGpreTowerOuterFactor]
      ring
    _ =
        (∑ d ∈ divisorSet,
          (nativeGpreCornerDivisorCoordinate
            c.cell c.corner c.arithmeticPrime.val c.time.val d : ℝ)) *
              outer := by
      rw [Finset.sum_mul]
    _ =
        (nativeGpreCornerReducedReadout
          c.cell c.corner c.arithmeticPrime.val c.time.val : ℝ) *
            nativeGpreTowerOuterFactor c := by
      rw [hsumR]

end

end CPFormal.Analytic.Cp
