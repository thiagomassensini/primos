import CPFormal.Analytic.CpNativeGpreJordanBounds

/-!
# Compilador local da majorante Jordan--H

A coordenada local do lift `G_pre` possui a forma aritmetica

`a * J - 2 * H`.

Este modulo isola a desigualdade universal consumida pelo ledger de norma. Ela
nao usa a definicao particular de `J` ou `H`: basta fornecer positividade,
`J ≤ D`, `H ≤ v D` e a incidencia `2v ≤ a`. O kernel deduz

`|a * J - 2 * H| ≤ a * D`.

A prova concreta de que os objetos aritmeticos nativos satisfazem essas quatro
hipoteses permanece separada; assim nao se esconde a etapa dificil dentro do
empacotamento funcional da constante `128`.
-/

namespace CPFormal.Analytic.Cp

/-- Dados locais suficientes para controlar a coordenada Jordan--H. -/
structure NativeGpreLocalJordanHBound
    (a J H v D : ℤ) : Prop where
  amplitude_nonneg : 0 ≤ a
  jordan_nonneg : 0 ≤ J
  jordan_le : J ≤ D
  h_nonneg : 0 ≤ H
  h_le_valuation : H ≤ v * D
  valuation_double_le_amplitude : 2 * v ≤ a
  scale_nonneg : 0 ≤ D

namespace NativeGpreLocalJordanHBound

/-- A cota `H ≤ vD`, junto de `2v ≤ a`, fornece `2H ≤ aD`. -/
theorem two_mul_h_le_amplitude_mul_scale
    {a J H v D : ℤ}
    (certificate : NativeGpreLocalJordanHBound a J H v D) :
    2 * H ≤ a * D := by
  have hfirst : 2 * H ≤ 2 * (v * D) :=
    mul_le_mul_of_nonneg_left certificate.h_le_valuation (by norm_num)
  have hsecond : (2 * v) * D ≤ a * D :=
    mul_le_mul_of_nonneg_right
      certificate.valuation_double_le_amplitude certificate.scale_nonneg
  calc
    2 * H ≤ 2 * (v * D) := hfirst
    _ = (2 * v) * D := by ring
    _ ≤ a * D := hsecond

/-- Majorante absoluta universal do bracket local. -/
theorem abs_bracket_le
    {a J H v D : ℤ}
    (certificate : NativeGpreLocalJordanHBound a J H v D) :
    |a * J - 2 * H| ≤ a * D := by
  rw [abs_le]
  constructor
  · have hAJ0 : 0 ≤ a * J :=
      mul_nonneg certificate.amplitude_nonneg certificate.jordan_nonneg
    have hneg : -(a * D) ≤ -(2 * H) :=
      neg_le_neg certificate.two_mul_h_le_amplitude_mul_scale
    have hshift : -(2 * H) ≤ a * J - 2 * H := by
      have h := add_le_add_right hAJ0 (-(2 * H))
      simpa [sub_eq_add_neg] using h
    exact hneg.trans hshift
  · have hAJD : a * J ≤ a * D :=
      mul_le_mul_of_nonneg_left certificate.jordan_le
        certificate.amplitude_nonneg
    have h2H0 : 0 ≤ 2 * H :=
      mul_nonneg (by norm_num) certificate.h_nonneg
    exact (sub_le_self (a * J) h2H0).trans hAJD

/-- Forma sem o parametro intermediario `v`, para consumidores que ja possuem
`2H ≤ aD` diretamente. -/
theorem abs_bracket_le_of_two_mul_h
    {a J H D : ℤ}
    (ha : 0 ≤ a) (hJ0 : 0 ≤ J) (hJD : J ≤ D)
    (hH0 : 0 ≤ H) (h2H : 2 * H ≤ a * D) :
    |a * J - 2 * H| ≤ a * D := by
  rw [abs_le]
  constructor
  · have hAJ0 : 0 ≤ a * J := mul_nonneg ha hJ0
    have hneg : -(a * D) ≤ -(2 * H) := neg_le_neg h2H
    have hshift : -(2 * H) ≤ a * J - 2 * H := by
      have h := add_le_add_right hAJ0 (-(2 * H))
      simpa [sub_eq_add_neg] using h
    exact hneg.trans hshift
  · have hAJD : a * J ≤ a * D :=
      mul_le_mul_of_nonneg_left hJD ha
    have h2H0 : 0 ≤ 2 * H := mul_nonneg (by norm_num) hH0
    exact (sub_le_self (a * J) h2H0).trans hAJD

end NativeGpreLocalJordanHBound

end CPFormal.Analytic.Cp