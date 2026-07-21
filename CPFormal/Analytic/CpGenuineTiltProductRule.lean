import CPFormal.Analytic.CpGenuineSecondDifferenceIdentity

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

end

end CPFormal.Analytic.Cp
