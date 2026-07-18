import CPFormal.Analytic.DirichletSecondDifference

/-!
# Convergencia da carta Cp bracketada em `re(s)>-1`

Aqui a estimativa de segunda diferenca e somada sobre os raios finitos da
camera e comparada com a p-serie

`(k+1)^(-re(s)-2)`.

O resultado deste modulo e a somabilidade absoluta dos blocos bracketados.
A identificacao finita deste bloco simetrico com `Genuine.Cp.bracket` e a
identidade analitica prolongada com o canal Genuine ficam em modulos
separados, para que convergencia e continuacao nao sejam misturadas.
-/

open scoped BigOperators

namespace CPFormal.Analytic.Cp

open CPFormal.Genuine.Cp

noncomputable section

/-- Segunda diferenca de raio natural na camera real centrada em `p(k+1)`. -/
def realCpPairBracket (p radius k : ℕ) (s : ℂ) : ℂ :=
  let center : ℝ := (p : ℝ) * ((k + 1 : ℕ) : ℝ)
  let r : ℝ := radius
  realDirichletPower s (center - r) -
    (2 • realDirichletPower s center) +
      realDirichletPower s (center + r)

/-- Soma dos pares de raios `1,...,halfRange(p)` no `k`-esimo centro. -/
def realCpSaturatedBracket (p k : ℕ) (s : ℂ) : ℂ :=
  ∑ radius ∈ Finset.Icc 1 (halfRange p),
    realCpPairBracket p radius k s

/-- A versao real da braquetada coincide com a segunda diferenca inteira. -/
theorem realCpPairBracket_eq_centeredSecondDifference
    (p radius k : ℕ) (s : ℂ) :
    realCpPairBracket p radius k s =
      CPFormal.centeredSecondDifference (dirichletTerm s)
        (alignedCenter p k) (radius : ℤ) := by
  simp [realCpPairBracket, realDirichletPower,
    CPFormal.centeredSecondDifference, dirichletTerm, alignedCenter]

/-- O bloco analitico e literalmente o `saturatedBracket` finito ja auditado. -/
theorem realCpSaturatedBracket_eq_saturatedBracket
    (p k : ℕ) (s : ℂ) :
    realCpSaturatedBracket p k s =
      CPFormal.saturatedBracket (halfRange p) (dirichletTerm s)
        (alignedCenter p k) := by
  classical
  unfold realCpSaturatedBracket CPFormal.saturatedBracket
  apply Finset.sum_congr rfl
  intro radius hradius
  exact realCpPairBracket_eq_centeredSecondDifference p radius k s

/-- Constante finita produzida pelas pernas de uma camera Cp. -/
def cpBracketMajorantConstant (p : ℕ) (s : ℂ) : ℝ :=
  ∑ radius ∈ Finset.Icc 1 (halfRange p),
    2 * ‖s * (s + 1)‖ * (radius : ℝ) ^ 2

/-- Um raio admissivel deixa o bordo esquerdo alem de `k+1`. -/
theorem natCast_add_one_le_alignedCenter_sub_radius
    {p radius k : ℕ} (hp : Nat.Prime p)
    (hradius : radius ≤ halfRange p) :
    ((k + 1 : ℕ) : ℝ) ≤
      (p : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ) := by
  have hhalf : halfRange p ≤ p - 1 := by
    unfold halfRange
    exact Nat.div_le_self (p - 1) 2
  have hradius' : radius ≤ p - 1 := le_trans hradius hhalf
  have hpone : 1 ≤ p := hp.one_le
  have hponeReal : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpone
  have hpnonneg : 0 ≤ (p : ℝ) - 1 := sub_nonneg.mpr hponeReal
  have hk : 1 ≤ ((k + 1 : ℕ) : ℝ) := by positivity
  have hradiusRealNat : (radius : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast hradius'
  have hpCast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hpone]
    norm_num
  have hradiusReal : (radius : ℝ) ≤ (p : ℝ) - 1 := by
    simpa [hpCast] using hradiusRealNat
  nlinarith [mul_nonneg hpnonneg (sub_nonneg.mpr hk)]

/--
Cota de uma unica braquetada: o centro `p(k+1)` pode ser substituido pelo
majorante mais simples `k+1`, uniformemente em `k`.
-/
theorem norm_realCpPairBracket_le
    {p radius k : ℕ} (hp : Nat.Prime p)
    {s : ℂ} (hs : -1 < s.re)
    (hradius : radius ∈ Finset.Icc 1 (halfRange p)) :
    ‖realCpPairBracket p radius k s‖ ≤
      (2 * ‖s * (s + 1)‖ * (radius : ℝ) ^ 2) *
        ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) := by
  have hleftLower :=
    natCast_add_one_le_alignedCenter_sub_radius hp hradius.2
  have hkpos : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  have hleft :
      0 < (p : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ) :=
    lt_of_lt_of_le hkpos hleftLower
  have hraw := norm_realDirichletPower_centeredSecondDifference_le
    hs (show 0 ≤ (radius : ℝ) by positivity) hleft
  have hpower :
      ((p : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ)) ^
          (-s.re - 2) ≤
        ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) :=
    Real.rpow_le_rpow_of_nonpos hkpos hleftLower (by linarith [hs])
  calc
    ‖realCpPairBracket p radius k s‖ ≤
        2 *
          (‖s * (s + 1)‖ *
            ((p : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ)) ^
              (-s.re - 2)) *
          (radius : ℝ) ^ 2 := by
      simpa [realCpPairBracket] using hraw
    _ = (2 * ‖s * (s + 1)‖ * (radius : ℝ) ^ 2) *
          (((p : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ)) ^
            (-s.re - 2)) := by ring
    _ ≤ (2 * ‖s * (s + 1)‖ * (radius : ℝ) ^ 2) *
          ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) :=
      mul_le_mul_of_nonneg_left hpower (by positivity)

/-- Cota de um bloco inteiro por uma unica p-serie. -/
theorem norm_realCpSaturatedBracket_le
    {p k : ℕ} (hp : Nat.Prime p)
    {s : ℂ} (hs : -1 < s.re) :
    ‖realCpSaturatedBracket p k s‖ ≤
      cpBracketMajorantConstant p s *
        ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) := by
  classical
  unfold realCpSaturatedBracket cpBracketMajorantConstant
  calc
    ‖∑ radius ∈ Finset.Icc 1 (halfRange p),
        realCpPairBracket p radius k s‖ ≤
        ∑ radius ∈ Finset.Icc 1 (halfRange p),
          ‖realCpPairBracket p radius k s‖ := norm_sum_le _ _
    _ ≤ ∑ radius ∈ Finset.Icc 1 (halfRange p),
          (2 * ‖s * (s + 1)‖ * (radius : ℝ) ^ 2) *
            ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) := by
      exact Finset.sum_le_sum fun radius hradius ↦
        norm_realCpPairBracket_le hp hs hradius
    _ = (∑ radius ∈ Finset.Icc 1 (halfRange p),
          2 * ‖s * (s + 1)‖ * (radius : ℝ) ^ 2) *
            ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) := by
      rw [Finset.sum_mul]

/-- A p-serie deslocada que domina a carta e somavel para `re(s)>-1`. -/
theorem summable_nat_add_one_rpow_neg_re_sub_two
    {s : ℂ} (hs : -1 < s.re) :
    Summable (fun k : ℕ ↦
      ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2)) := by
  have hbase : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-s.re - 2)) :=
    Real.summable_nat_rpow.mpr (by linarith [hs])
  have hshift := hbase.comp_injective
    (show Function.Injective (fun n : ℕ ↦ n + 1) by
      intro a b hab
      exact Nat.add_right_cancel hab)
  simpa [Function.comp_def] using hshift

/-!
Teorema central deste checkpoint: as normas dos blocos bracketados formam
uma serie somavel em todo o semiplano aberto `re(s)>-1`.
-/
theorem summable_norm_realCpSaturatedBracket
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : -1 < s.re) :
    Summable (fun k : ℕ ↦ ‖realCpSaturatedBracket p k s‖) := by
  have hpower := summable_nat_add_one_rpow_neg_re_sub_two hs
  have hmajorant := hpower.mul_left (cpBracketMajorantConstant p s)
  exact hmajorant.of_norm_bounded
    (fun k ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact norm_realCpSaturatedBracket_le hp hs)

/-- A serie complexa converge como consequencia de sua somabilidade absoluta. -/
theorem summable_realCpSaturatedBracket
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : -1 < s.re) :
    Summable (fun k : ℕ ↦ realCpSaturatedBracket p k s) :=
  (summable_norm_realCpSaturatedBracket p hp hs).of_norm

/-- A carta bracketada convergente, com a semente finita mantida explicita. -/
def bracketedDirichletChart (p : ℕ) (s : ℂ) : ℂ :=
  CPFormal.Genuine.Cp.seedSum p (dirichletTerm s) +
    ∑' k : ℕ, realCpSaturatedBracket p k s

/-- Prefixo finito da mesma carta, antes da passagem ao limite. -/
def finiteBracketedDirichletChart (p M : ℕ) (s : ℂ) : ℂ :=
  CPFormal.Genuine.Cp.seedSum p (dirichletTerm s) +
    ∑ k ∈ Finset.range M, realCpSaturatedBracket p k s

/-- Passagem ao limite dos prefixos bracketados no dominio `re(s)>-1`. -/
theorem finiteBracketedDirichletChart_tendsto
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : -1 < s.re) :
    Filter.Tendsto (fun M : ℕ ↦ finiteBracketedDirichletChart p M s)
      Filter.atTop (nhds (bracketedDirichletChart p s)) := by
  have hsum := (summable_realCpSaturatedBracket p hp hs).tendsto_sum_tsum_nat
  simpa [finiteBracketedDirichletChart, bracketedDirichletChart] using
    tendsto_const_nhds.add hsum

end

end CPFormal.Analytic.Cp
