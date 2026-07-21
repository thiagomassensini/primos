import CPFormal.Analytic.CpGenuineSecondDifferenceIdentity
import CPFormal.Analytic.CpBracketGreenBoundary

/-!
# Regra de produto entre o bracket Genuine e o tilt transversal

O bracket local que aparece no `genuineContinuation` e o tilt de carry usam
o mesmo stencil de segunda diferenca, mas nao atuam sobre o mesmo campo. Este
modulo abre exatamente essa diferenca.

Para `s = sigma + I t` e `delta = sigma - 1/2`, escrevemos no eixo positivo

`x^(-s) = x^(-1/2-I t) * x^(-delta)`.

A regra discreta de Leibniz mostra que o bracket do produto possui quatro
canais: tilt radial ponderado, curvatura do carrier critico e dois termos
cruzados de primeira diferenca. Portanto transportar um zero Genuine ate o
kernel do tilt exige controlar os tres canais nao radiais; eles nao podem ser
apagados por identificacao de operadores.
-/

open scoped BigOperators

namespace CPFormal

variable {R : Type*} [CommRing R]

/-- Regra de Leibniz exata para a segunda diferenca centrada de um produto. -/
theorem centeredSecondDifference_mul
    (f g : ℤ → R) (center radius : ℤ) :
    centeredSecondDifference (fun n ↦ f n * g n) center radius =
      f center * centeredSecondDifference g center radius +
        g center * centeredSecondDifference f center radius +
        (f (center - radius) - f center) *
          (g (center - radius) - g center) +
        (f (center + radius) - f center) *
          (g (center + radius) - g center) := by
  unfold centeredSecondDifference
  simp only [nsmul_eq_mul]
  ring

end CPFormal

namespace CPFormal.Analytic.Cp

noncomputable section

/-!
## Fatoracao radial no eixo positivo
-/

/-- Carrier que contem a escala critica `1/2` e toda a fase vertical. -/
def criticalLineDirichletCarrier (s : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (-((1 : ℂ) / 2 + Complex.I * s.im))

/-- Perfil de Dirichlet visto em offsets inteiros ao redor de um centro real. -/
def localDirichletProfile (s : ℂ) (center : ℝ) (offset : ℤ) : ℂ :=
  realDirichletPower s (center + (offset : ℝ))

/-- Carrier critico visto nos mesmos offsets inteiros. -/
def localCriticalLineCarrier
    (s : ℂ) (center : ℝ) (offset : ℤ) : ℂ :=
  criticalLineDirichletCarrier s (center + (offset : ℝ))

/-- Complexificacao do perfil transversal real usado pelo tilt. -/
def complexTransversePowerProfile
    (delta center : ℝ) (offset : ℤ) : ℂ :=
  (transversePowerProfile delta center offset : ℂ)

/--
Fatoracao pontual do monomio completo em carrier critico e perfil radial.
A positividade de `x` elimina qualquer ambiguidade de ramo da potencia.
-/
theorem realDirichletPower_eq_criticalLineCarrier_mul_transverse
    (s : ℂ) {x : ℝ} (hx : 0 < x) :
    realDirichletPower s x =
      criticalLineDirichletCarrier s x *
        (((x ^ (-criticalDisplacement s.re) : ℝ)) : ℂ) := by
  have hxComplex : (x : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hx
  have hexponent :
      -((1 : ℂ) / 2 + Complex.I * s.im) +
          ((-criticalDisplacement s.re : ℝ) : ℂ) =
        -s := by
    apply Complex.ext
    · simp [criticalDisplacement]
      ring
    · simp
  unfold realDirichletPower criticalLineDirichletCarrier
  rw [Complex.ofReal_cpow hx.le]
  rw [← Complex.cpow_add _ _ hxComplex]
  rw [hexponent]

/-- A mesma fatoracao escrita no carrier local de offsets. -/
theorem localDirichletProfile_eq_carrier_mul_transverse
    (s : ℂ) (center : ℝ) {offset : ℤ}
    (hpos : 0 < center + (offset : ℝ)) :
    localDirichletProfile s center offset =
      localCriticalLineCarrier s center offset *
        complexTransversePowerProfile
          (criticalDisplacement s.re) center offset := by
  exact realDirichletPower_eq_criticalLineCarrier_mul_transverse
    s hpos

/-!
## Os quatro canais da segunda diferenca
-/

/-- A complexificacao preserva exatamente a segunda diferenca do tilt. -/
theorem centeredSecondDifference_complexTransversePowerProfile
    (delta center : ℝ) (radius : ℤ) :
    CPFormal.centeredSecondDifference
        (complexTransversePowerProfile delta center) 0 radius =
      (cpPairTilt delta center radius : ℂ) := by
  rw [cpPairTilt_eq_centeredSecondDifference]
  simp [complexTransversePowerProfile,
    CPFormal.centeredSecondDifference]

/-- Curvatura do carrier critico, ponderada pelo valor radial central. -/
def localCriticalCarrierCurvature
    (s : ℂ) (center : ℝ) (radius : ℤ) : ℂ :=
  complexTransversePowerProfile
      (criticalDisplacement s.re) center 0 *
    CPFormal.centeredSecondDifference
      (localCriticalLineCarrier s center) 0 radius

/--
Dois termos cruzados de primeira diferenca produzidos pela regra de Leibniz.
-/
def localCriticalCarrierCross
    (s : ℂ) (center : ℝ) (radius : ℤ) : ℂ :=
  (localCriticalLineCarrier s center (-radius) -
      localCriticalLineCarrier s center 0) *
    (complexTransversePowerProfile
        (criticalDisplacement s.re) center (-radius) -
      complexTransversePowerProfile
        (criticalDisplacement s.re) center 0) +
  (localCriticalLineCarrier s center radius -
      localCriticalLineCarrier s center 0) *
    (complexTransversePowerProfile
        (criticalDisplacement s.re) center radius -
      complexTransversePowerProfile
        (criticalDisplacement s.re) center 0)

/--
Decomposicao local `same-s` do bracket Genuine. O primeiro termo e exatamente
o tilt radial, mas ponderado pelo carrier complexo central. Os outros dois
canais sao explicitamente tipados e permanecem no ledger.
-/
theorem centeredSecondDifference_localDirichletProfile_eq_weightedTilt_add_carrier
    (s : ℂ) {center : ℝ} {radius : ℤ}
    (hleft : 0 < center - (radius : ℝ))
    (hcenter : 0 < center)
    (hright : 0 < center + (radius : ℝ)) :
    CPFormal.centeredSecondDifference
        (localDirichletProfile s center) 0 radius =
      localCriticalLineCarrier s center 0 *
          (cpPairTilt (criticalDisplacement s.re) center radius : ℂ) +
        localCriticalCarrierCurvature s center radius +
        localCriticalCarrierCross s center radius := by
  let carrier : ℤ → ℂ := localCriticalLineCarrier s center
  let radial : ℤ → ℂ :=
    complexTransversePowerProfile (criticalDisplacement s.re) center
  have hminus :
      localDirichletProfile s center (-radius) =
        carrier (-radius) * radial (-radius) := by
    exact localDirichletProfile_eq_carrier_mul_transverse
      s center (by simpa using hleft)
  have hzero :
      localDirichletProfile s center 0 = carrier 0 * radial 0 := by
    exact localDirichletProfile_eq_carrier_mul_transverse
      s center (by simpa using hcenter)
  have hplus :
      localDirichletProfile s center radius =
        carrier radius * radial radius := by
    exact localDirichletProfile_eq_carrier_mul_transverse
      s center hright
  calc
    CPFormal.centeredSecondDifference
        (localDirichletProfile s center) 0 radius =
      CPFormal.centeredSecondDifference
        (fun offset ↦ carrier offset * radial offset) 0 radius := by
          simp only [CPFormal.centeredSecondDifference, zero_sub, zero_add]
          rw [hminus, hzero, hplus]
    _ = carrier 0 *
          CPFormal.centeredSecondDifference radial 0 radius +
        radial 0 *
          CPFormal.centeredSecondDifference carrier 0 radius +
        (carrier (-radius) - carrier 0) *
          (radial (-radius) - radial 0) +
        (carrier radius - carrier 0) *
          (radial radius - radial 0) := by
      simpa using
        (CPFormal.centeredSecondDifference_mul carrier radial 0 radius)
    _ = localCriticalLineCarrier s center 0 *
          (cpPairTilt (criticalDisplacement s.re) center radius : ℂ) +
        localCriticalCarrierCurvature s center radius +
        localCriticalCarrierCross s center radius := by
      rw [centeredSecondDifference_complexTransversePowerProfile]
      dsimp [carrier, radial, localCriticalCarrierCurvature,
        localCriticalCarrierCross]
      ring

/-!
## Especializacao aos blocos aritmeticos Genuine
-/

/--
Cada par real da camera Genuine possui a mesma decomposicao em quatro canais.
O limite esquerdo permanece positivo para todo raio admissivel da camera.
-/
theorem realCpPairBracket_eq_weightedTiltPair_add_carrier
    (p radius k : ℕ) (hp : Nat.Prime p)
    (hradius : radius ≤ CPFormal.Genuine.Cp.halfRange p)
    (s : ℂ) :
    realCpPairBracket p radius k s =
      localCriticalLineCarrier s
          ((p : ℝ) * ((k + 1 : ℕ) : ℝ)) 0 *
        (cpPairTilt (criticalDisplacement s.re)
          ((p : ℝ) * ((k + 1 : ℕ) : ℝ)) (radius : ℤ) : ℂ) +
      localCriticalCarrierCurvature s
        ((p : ℝ) * ((k + 1 : ℕ) : ℝ)) (radius : ℤ) +
      localCriticalCarrierCross s
        ((p : ℝ) * ((k + 1 : ℕ) : ℝ)) (radius : ℤ) := by
  let center : ℝ := (p : ℝ) * ((k + 1 : ℕ) : ℝ)
  have hkpos : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  have hleftBound :
      ((k + 1 : ℕ) : ℝ) ≤ center - (radius : ℝ) := by
    simpa [center] using
      (natCast_add_one_le_alignedCenter_sub_radius hp hradius)
  have hleft : 0 < center - (radius : ℝ) :=
    lt_of_lt_of_le hkpos hleftBound
  have hpReal : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hcenter : 0 < center := by
    dsimp [center]
    exact mul_pos hpReal hkpos
  have hradiusNonneg : 0 ≤ (radius : ℝ) := by positivity
  have hright : 0 < center + (radius : ℝ) :=
    lt_of_lt_of_le hcenter (le_add_of_nonneg_right hradiusNonneg)
  simpa [realCpPairBracket, localDirichletProfile, center,
    CPFormal.centeredSecondDifference, sub_eq_add_neg] using
    (centeredSecondDifference_localDirichletProfile_eq_weightedTilt_add_carrier
      s hleft hcenter hright)

/-- Na camera canonica, o tilt inteiro e o unico par de raio `1`. -/
theorem cpTilt_three_eq_cpPairTilt_one
    (delta center : ℝ) :
    cpTilt 3 delta center = cpPairTilt delta center 1 := by
  rw [cpTilt_eq_saturatedBracket 3 (by norm_num) (by norm_num)]
  simpa [CPFormal.saturatedBracket, CPFormal.Genuine.Cp.halfRange] using
    (cpPairTilt_eq_centeredSecondDifference delta center 1).symm

/-- Centro real do `k`-esimo bloco da camera canonica `p = 3`. -/
def canonicalRealCpCenter (k : ℕ) : ℝ :=
  (3 : ℝ) * ((k + 1 : ℕ) : ℝ)

/-- Parcela de tilt ponderada pelo carrier critico na camera canonica. -/
def canonicalCriticalWeightedTiltBlock (k : ℕ) (s : ℂ) : ℂ :=
  localCriticalLineCarrier s (canonicalRealCpCenter k) 0 *
    (cpTilt 3 (criticalDisplacement s.re) (canonicalRealCpCenter k) : ℂ)

/-- Curvatura do carrier e cruzamentos no unico raio da camera canonica. -/
def canonicalCriticalCarrierRemainderBlock (k : ℕ) (s : ℂ) : ℂ :=
  localCriticalCarrierCurvature s (canonicalRealCpCenter k) 1 +
    localCriticalCarrierCross s (canonicalRealCpCenter k) 1

/--
Cada bloco Genuine canonico e tilt ponderado mais o remainder de carrier.
Esta igualdade usa o monomio completo `n^(-s)` no lado esquerdo.
-/
theorem realCpSaturatedBracket_three_eq_weightedTilt_add_carrierRemainder
    (k : ℕ) (s : ℂ) :
    realCpSaturatedBracket 3 k s =
      canonicalCriticalWeightedTiltBlock k s +
        canonicalCriticalCarrierRemainderBlock k s := by
  rw [show realCpSaturatedBracket 3 k s =
      realCpPairBracket 3 1 k s by
    simp [realCpSaturatedBracket, CPFormal.Genuine.Cp.halfRange]]
  rw [realCpPairBracket_eq_weightedTiltPair_add_carrier
    3 1 k (by norm_num)
      (by norm_num [CPFormal.Genuine.Cp.halfRange]) s]
  unfold canonicalCriticalWeightedTiltBlock
    canonicalCriticalCarrierRemainderBlock canonicalRealCpCenter
  rw [cpTilt_three_eq_cpPairTilt_one]
  ring

/-!
## Ledger finito e leitura de um zero Genuine
-/

/-- Soma finita dos tilts ponderados pelos carriers criticos. -/
def finiteCanonicalCriticalWeightedTiltTrace (M : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.range M, canonicalCriticalWeightedTiltBlock k s

/-- Soma finita dos canais de curvatura e cruzamento do carrier. -/
def finiteCanonicalCriticalCarrierRemainderTrace
    (M : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.range M, canonicalCriticalCarrierRemainderBlock k s

/--
Ledger `same-s` finito: o traco bracketado canonico separa exatamente o tilt
ponderado e o remainder do carrier, antes de qualquer sintese escalar.
-/
theorem finiteCanonicalBracketTrace_eq_weightedTilt_add_carrierRemainder
    (M : ℕ) (s : ℂ) :
    finiteCanonicalBracketTrace M s =
      finiteCanonicalCriticalWeightedTiltTrace M s +
        finiteCanonicalCriticalCarrierRemainderTrace M s := by
  unfold finiteCanonicalBracketTrace
    finiteCanonicalCriticalWeightedTiltTrace
    finiteCanonicalCriticalCarrierRemainderTrace
  calc
    (∑ k ∈ Finset.range M, realCpSaturatedBracket 3 k s) =
        ∑ k ∈ Finset.range M,
          (canonicalCriticalWeightedTiltBlock k s +
            canonicalCriticalCarrierRemainderBlock k s) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact
        realCpSaturatedBracket_three_eq_weightedTilt_add_carrierRemainder
          k s
    _ = (∑ k ∈ Finset.range M,
          canonicalCriticalWeightedTiltBlock k s) +
        ∑ k ∈ Finset.range M,
          canonicalCriticalCarrierRemainderBlock k s := by
      exact Finset.sum_add_distrib

/--
Num zero Genuine, o ledger `tilt ponderado + carrier` converge exatamente a
`-1`. Esta e a equacao global realmente fornecida pelo zero; separar o tilt
do remainder requer uma estimativa nova e nao uma simplificacao algebrica.
-/
theorem finiteCanonicalWeightedTilt_add_carrierRemainder_tendsto_neg_one_of_genuine_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Filter.Tendsto
      (fun M : ℕ ↦
        finiteCanonicalCriticalWeightedTiltTrace M s +
          finiteCanonicalCriticalCarrierRemainderTrace M s)
      Filter.atTop (nhds (-1)) := by
  have hsum :=
    (summable_realCpSaturatedBracket 3 (by norm_num)
      (by linarith [hs.1])).tendsto_sum_tsum_nat
  have htrace : canonicalBracketTrace s = -1 :=
    canonicalBracketTrace_eq_neg_one_of_genuineContinuation_zero hs hzero
  have hfinite :
      Filter.Tendsto
        (fun M : ℕ ↦ finiteCanonicalBracketTrace M s)
        Filter.atTop (nhds (canonicalBracketTrace s)) := by
    simpa [finiteCanonicalBracketTrace, canonicalBracketTrace] using hsum
  rw [htrace] at hfinite
  simpa only
    [finiteCanonicalBracketTrace_eq_weightedTilt_add_carrierRemainder]
    using hfinite

end

end CPFormal.Analytic.Cp
