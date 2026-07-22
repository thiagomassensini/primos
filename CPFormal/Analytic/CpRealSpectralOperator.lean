import CPFormal.Analytic.CpFiniteTfvdLogJetCriticalPhaseFan

/-!
# Fatia espectral real intrinseca do Genuine

A geometria de carry fixa a amplitude critica. Este modulo nomeia a restricao
real restante sem redefinir o campo de Dirichlet, as cartas ou o Genuine:

`realSpectralState t n = (n+1)^(-(1/2 + t*I))`.

Assim `t : ℝ` parametriza somente a rotacao de fase; os valores continuam em
`ℂ`, o plano real de amplitudes com fase. O modulo registra no kernel que:

* a norma de cada estado e exatamente `(n+1)^(-1/2)`;
* a fatia pertence ao strip Genuine e e fixa pela reflexao espectral;
* o fator real-espectral da camera e o `cpChartFactor` ja existente;
* a corrente finita e literalmente a carta bracketada/Genuine do mesmo corte;
* todas as cameras primas impares infinitas recuperam o mesmo Genuine.

Nenhum zero, tabela espectral, refinamento numerico ou conclusao Green e usado.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Estado no vertice positivo `n+1`, com amplitude critica fixada pelo carry
e parametro espectral estritamente real. -/
def realSpectralState (t : ℝ) (n : ℕ) : ℂ :=
  positiveDirichletValue (criticalLineParameter t) n

/-- O parametro real altera somente a fase: a amplitude e `1/sqrt(n+1)`. -/
@[simp] theorem norm_realSpectralState (t : ℝ) (n : ℕ) :
    ‖realSpectralState t n‖ =
      (((n + 1 : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ)) := by
  simpa [realSpectralState] using
    (norm_positiveDirichletValue (criticalLineParameter t) n)

/-- A orbita real critica permanece no interior do strip Genuine. -/
@[simp] theorem criticalLineParameter_mem_genuineCriticalStrip (t : ℝ) :
    criticalLineParameter t ∈ genuineCriticalStrip := by
  change 0 < (criticalLineParameter t).re ∧
    (criticalLineParameter t).re < 1
  constructor <;> norm_num

/-- A reflexao espectral fixa ponto a ponto a orbita real critica. -/
@[simp] theorem reflectedParameter_criticalLineParameter (t : ℝ) :
    reflectedParameter (criticalLineParameter t) = criticalLineParameter t := by
  exact reflectedParameter_eq_self_of_re_eq_half (criticalLineParameter_re t)

/-- Restricao real do fator de calibracao de uma camera prima. -/
def realSpectralChartFactor (p : ℕ) (t : ℝ) : ℂ :=
  cpChartFactor p (criticalLineParameter t)

/-- O fator de uma camera prima nunca zera na orbita real critica. -/
theorem realSpectralChartFactor_ne_zero
    (p : ℕ) (hp : Nat.Prime p) (t : ℝ) :
    realSpectralChartFactor p t ≠ 0 := by
  simpa [realSpectralChartFactor] using
    (cpChartFactor_ne_zero_on_genuineCriticalStrip p hp
      (criticalLineParameter_mem_genuineCriticalStrip t))

/-- Corrente finita de sementes e brackets na camera `p`, no corte `M`. -/
def finiteRealSpectralChart (p M : ℕ) (t : ℝ) : ℂ :=
  finiteBracketedDirichletChart p M (criticalLineParameter t)

/-- A corrente real-espectral finita e literalmente a carta Genuine finita. -/
theorem finiteRealSpectralChart_eq_finiteChart
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) (t : ℝ) :
    finiteRealSpectralChart p M t =
      CPFormal.Genuine.Cp.finiteChart p M
        (dirichletTerm (criticalLineParameter t)) := by
  exact finiteBracketedDirichletChart_eq_finiteChart
    p M hp hpodd (criticalLineParameter t)

/-- Camera finita normalizada pelo seu fator de bordo. -/
def finiteRealSpectralCamera (p M : ℕ) (t : ℝ) : ℂ :=
  finiteRealSpectralChart p M t / realSpectralChartFactor p t

/-- Camera infinita normalizada na orbita espectral real. -/
def realSpectralCamera (p : ℕ) (t : ℝ) : ℂ :=
  cpGenuineQuotient p (criticalLineParameter t)

/-- Genuine canonico visto como funcao do parametro real de fase. -/
def realSpectralGenuine (t : ℝ) : ℂ :=
  genuineContinuation (criticalLineParameter t)

/-- Toda camera prima impar infinita e o mesmo Genuine real-espectral. -/
theorem realSpectralCamera_eq_realSpectralGenuine
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) (t : ℝ) :
    realSpectralCamera p t = realSpectralGenuine t := by
  simpa [realSpectralCamera, realSpectralGenuine] using
    (cpGenuineQuotient_eq_genuineContinuation p hp hpodd
      (criticalLineParameter_mem_genuineCriticalStrip t))

/-- Independencia literal da camera prima na fatia real. -/
theorem realSpectralCamera_prime_independent
    (p q : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    (t : ℝ) :
    realSpectralCamera p t = realSpectralCamera q t := by
  rw [realSpectralCamera_eq_realSpectralGenuine p hp hpodd t,
    realSpectralCamera_eq_realSpectralGenuine q hq hqodd t]

/-- A carta bracketada na orbita real e fator vezes Genuine, sem usar zeros. -/
theorem bracketedDirichletChart_criticalLine_eq_factor_mul_realSpectralGenuine
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) (t : ℝ) :
    bracketedDirichletChart p (criticalLineParameter t) =
      realSpectralChartFactor p t * realSpectralGenuine t := by
  simpa [realSpectralChartFactor, realSpectralGenuine] using
    (bracketedDirichletChart_eq_cpChartFactor_mul_genuineContinuation
      p hp hpodd (criticalLineParameter_mem_genuineCriticalStrip t))

/-- Na fatia real, zerar uma carta prima e zerar o Genuine sao a mesma condicao. -/
theorem bracketedDirichletChart_criticalLine_zero_iff_realSpectralGenuine_zero
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) (t : ℝ) :
    bracketedDirichletChart p (criticalLineParameter t) = 0 ↔
      realSpectralGenuine t = 0 := by
  simpa [realSpectralGenuine] using
    (bracketedDirichletChart_zero_iff_genuineContinuation_zero
      p hp hpodd (criticalLineParameter_mem_genuineCriticalStrip t))

end

end CPFormal.Analytic.Cp
