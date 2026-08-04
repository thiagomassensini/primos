import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# O invariante adimensional da compressão do carry

A seleção `σ = 1/2` da teoria da compressão do carry **não** é um fato de análise
complexa, de operadores ou de zeros.  É um invariante estrutural, anterior a
qualquer representação (`ℝ²`, `ℂ`, ...).  Este módulo isola esse núcleo na sua
forma mais nua.

Na coordenada de escala `x = k·log b`, a igualdade energia = massa é

`exp(-(2σ)·x) = exp(-x)`,

e, para toda escala `x > 0`, ela vale **exatamente** em `σ = 1/2`
(`scaleQuadraticCompatible_iff`).  A base desaparece: qualquer base `b > 1` e
qualquer profundidade `k > 0` reduzem-se a essa mesma equação
(`baseQuadraticCompatible_iff`), e por isso o locus de compatibilidade é o mesmo
para todas as bases e profundidades (`quadraticCompatible_locus_base_independent`).

> A câmera muda `log b`; a lei `2σ = 1` permanece.  É o que não muda quando tudo
> muda.

Genuine First: nenhum zeta, equação funcional ou RH.
-/

namespace CPFormal.Analytic.Cp

/-- **Núcleo adimensional.**  Na coordenada de escala `x > 0`, a energia quadrática
iguala a massa exatamente no ponto fixo autodual `σ = 1/2` — sem referência a
base, dígito ou representação. -/
theorem scaleQuadraticCompatible_iff {x : ℝ} (hx : 0 < x) {σ : ℝ} :
    Real.exp (-(2 * σ) * x) = Real.exp (-x) ↔ σ = 1 / 2 := by
  rw [Real.exp_eq_exp]
  constructor
  · intro h
    have h2 : (2 * σ - 1) * x = 0 := by linear_combination -h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linarith
    · exact absurd h3 (ne_of_gt hx)
  · intro h; rw [h]; ring

/-- **Redução da base à escala.**  A lei concreta em base `b > 1` e profundidade
`k > 0`, `b^{-2σk} = b^{-k}`, é a lei adimensional na escala `x = k·log b`; logo
vale exatamente em `σ = 1/2`. -/
theorem baseQuadraticCompatible_iff {b : ℝ} (hb : 1 < b) {k : ℕ} (hk : 0 < k)
    {σ : ℝ} :
    b ^ (-(2 * σ) * (k : ℝ)) = b ^ (-(k : ℝ)) ↔ σ = 1 / 2 := by
  have hb0 : 0 < b := by linarith
  have hlogb : 0 < Real.log b := Real.log_pos hb
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  have hx : 0 < (k : ℝ) * Real.log b := by positivity
  rw [Real.rpow_def_of_pos hb0, Real.rpow_def_of_pos hb0,
    show Real.log b * (-(2 * σ) * (k : ℝ)) = -(2 * σ) * ((k : ℝ) * Real.log b) by
      ring,
    show Real.log b * (-(k : ℝ)) = -((k : ℝ) * Real.log b) by ring]
  exact scaleQuadraticCompatible_iff hx

/-- **O que não muda quando tudo muda.**  O locus de compatibilidade quadrática é
literalmente o mesmo para quaisquer bases `b, c > 1` e profundidades `j, k > 0`:
ambas as leis concretas são a mesma equação adimensional `2σ = 1`. -/
theorem quadraticCompatible_locus_base_independent
    {b c : ℝ} (hb : 1 < b) (hc : 1 < c) {j k : ℕ} (hj : 0 < j) (hk : 0 < k)
    {σ : ℝ} :
    (b ^ (-(2 * σ) * (j : ℝ)) = b ^ (-(j : ℝ))) ↔
      (c ^ (-(2 * σ) * (k : ℝ)) = c ^ (-(k : ℝ))) := by
  rw [baseQuadraticCompatible_iff hb hj, baseQuadraticCompatible_iff hc hk]

end CPFormal.Analytic.Cp
