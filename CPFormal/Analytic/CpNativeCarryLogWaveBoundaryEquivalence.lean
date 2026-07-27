import CPFormal.Analytic.CpNativeCarryWeightedSpectralState

/-!
# Native log-wave eigen-boundary equivalence

The critical carry amplitude and logarithmic phase define the entire log-coordinate
wave

`phi_z(u) = exp (-(1/2 + z I) u)`.

The fixed first-order dilation expression, evaluated on the canonical
logarithmic derivative channel of this wave,

`D(phi_z) = I * (-(1/2 + z I) phi_z) + (I/2) * phi_z`,

satisfies `D(phi_z) = z phi_z`.  Thus `z` is the linear characteristic
parameter of the interior equation, rather than the scalar value of a readout.

The arithmetic camera is imposed separately as one fixed bracket boundary
condition: apply the existing finite Cp chart to the positive-integer samples of
the same wave and require those cutoffs to converge to zero.

Inside the Genuine strip, the Lean kernel proves that this eigen-equation plus
boundary closure is equivalent to a native complex-time Genuine resonance.  No
self-adjointness or zero localization is assumed.  The separate calculus
certificate for the displayed derivative formula is not needed by this
algebraic/spectral equivalence and is deliberately left outside this module.
The remaining operator task is to realize the fixed dilation expression and
fixed bracket boundary as a self-adjoint closed relation.
-/

open scoped Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-- Native wave in the logarithmic coordinate. -/
def nativeCarryLogWave (z u : ℂ) : ℂ :=
  Complex.exp (-(carryComplexTimeParameter z) * u)

/-- The fixed first-order dilation expression evaluated from a value and its
canonical logarithmic derivative channel. -/
def nativeCarryLogDilationExpression (value derivative : ℂ) : ℂ :=
  Complex.I * derivative + (Complex.I / 2) * value

/-- The native wave solves the fixed linear interior equation with characteristic
parameter `z`. -/
theorem nativeCarryLogDilationExpression_wave_eq
    (z u : ℂ) :
    nativeCarryLogDilationExpression
        (nativeCarryLogWave z u)
        (-(carryComplexTimeParameter z) * nativeCarryLogWave z u) =
      z * nativeCarryLogWave z u := by
  have hzi : (-Complex.I * z) * Complex.I = z := by
    calc
      (-Complex.I * z) * Complex.I =
          -z * (Complex.I * Complex.I) := by ring
      _ = -z * (-1) := by rw [Complex.I_mul_I]
      _ = z := by ring
  have hhalf : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by
    norm_num
  have hcoeff :
      (-Complex.I) * (((1 / 2 : ℝ) : ℂ) + z * Complex.I) +
          Complex.I / 2 = z := by
    calc
      (-Complex.I) * (((1 / 2 : ℝ) : ℂ) + z * Complex.I) +
          Complex.I / 2 =
        (-Complex.I) * ((1 / 2 : ℝ) : ℂ) +
          (-Complex.I * z) * Complex.I + Complex.I / 2 := by ring
      _ = (-Complex.I) * ((1 / 2 : ℝ) : ℂ) + z +
          Complex.I / 2 := by rw [hzi]
      _ = z := by rw [hhalf]; ring
  unfold nativeCarryLogDilationExpression carryComplexTimeParameter
  calc
    Complex.I *
          (-((((1 / 2 : ℝ) : ℂ) + z * Complex.I)) *
            nativeCarryLogWave z u) +
        Complex.I / 2 * nativeCarryLogWave z u =
      ((-Complex.I) * (((1 / 2 : ℝ) : ℂ) + z * Complex.I) +
          Complex.I / 2) * nativeCarryLogWave z u := by ring
    _ = z * nativeCarryLogWave z u := by rw [hcoeff]

/-- Positive-integer samples of the log wave are exactly the Dirichlet monomials
used by the bracket camera. -/
theorem nativeCarryLogWave_log_nat_eq_dirichletTerm
    (z : ℂ) (n : ℕ) (hn : 0 < n) :
    nativeCarryLogWave z ((Real.log n : ℝ) : ℂ) =
      dirichletTerm (carryComplexTimeParameter z) (n : ℤ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnC : ((n : ℂ) ≠ 0) := by exact_mod_cast (Nat.ne_of_gt hn)
  have hlog :
      Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) :=
    (Complex.ofReal_log hnR.le).symm
  unfold nativeCarryLogWave dirichletTerm
  change
    Complex.exp
        (-(carryComplexTimeParameter z) * (Real.log (n : ℝ) : ℂ)) =
      (n : ℂ) ^ (-(carryComplexTimeParameter z))
  rw [Complex.cpow_def_of_ne_zero hnC, hlog]
  congr 1
  ring

/-- The integer sample field consumed by the already formalized finite bracket
camera.  The camera itself remains fixed; only the native wave varies with `z`. -/
def nativeCarryLogWaveIntegerSample (z : ℂ) : ℤ → ℂ :=
  dirichletTerm (carryComplexTimeParameter z)

/-- Fixed bracket boundary closure of the native log wave. -/
def NativeCarryLogWaveBoundaryCloses (z : ℂ) : Prop :=
  Tendsto
    (fun M : ℕ =>
      CPFormal.Genuine.Cp.finiteChart 3 M
        (nativeCarryLogWaveIntegerSample z))
    atTop (nhds 0)

/-- The complete native characteristic boundary problem: the fixed dilation
expression has eigenparameter `z`, and the fixed bracket boundary closes. -/
def NativeCarryLogWaveCharacteristic (z : ℂ) : Prop :=
  (∀ u : ℂ,
    nativeCarryLogDilationExpression
        (nativeCarryLogWave z u)
        (-(carryComplexTimeParameter z) * nativeCarryLogWave z u) =
      z * nativeCarryLogWave z u) ∧
  NativeCarryLogWaveBoundaryCloses z

/-- Boundary closure of the native wave is exactly scalar Genuine resonance in
the open strip. -/
theorem nativeCarryLogWaveBoundaryCloses_iff_resonance
    {z : ℂ} (hz : carryComplexTimeParameter z ∈ genuineCriticalStrip) :
    NativeCarryLogWaveBoundaryCloses z ↔
      IsNativeCarryComplexTimeResonance z := by
  let s : ℂ := carryComplexTimeParameter z
  have hhalf : -1 < s.re := by
    dsimp [s]
    linarith [hz.1]
  have hlimit :
      Tendsto
        (fun M : ℕ =>
          CPFormal.Genuine.Cp.finiteChart 3 M (dirichletTerm s))
        atTop (nhds (bracketedDirichletChart 3 s)) :=
    finiteChart_dirichlet_tendsto_bracketedDirichletChart
      3 (by norm_num) (by norm_num) hhalf
  have hzeroIff :
      bracketedDirichletChart 3 s = 0 ↔ genuineContinuation s = 0 :=
    bracketedDirichletChart_zero_iff_genuineContinuation_zero
      3 (by norm_num) (by norm_num) hz
  constructor
  · intro hboundary
    have hboundary' :
        Tendsto
          (fun M : ℕ =>
            CPFormal.Genuine.Cp.finiteChart 3 M (dirichletTerm s))
          atTop (nhds 0) := by
      simpa [NativeCarryLogWaveBoundaryCloses,
        nativeCarryLogWaveIntegerSample, s] using hboundary
    have hchart : bracketedDirichletChart 3 s = 0 :=
      tendsto_nhds_unique hlimit hboundary'
    unfold IsNativeCarryComplexTimeResonance carryComplexTimeGenuine
    simpa [s] using hzeroIff.mp hchart
  · intro hres
    have hchart : bracketedDirichletChart 3 s = 0 := by
      apply hzeroIff.mpr
      unfold IsNativeCarryComplexTimeResonance carryComplexTimeGenuine at hres
      simpa [s] using hres
    have hzeroLimit :
        Tendsto
          (fun M : ℕ =>
            CPFormal.Genuine.Cp.finiteChart 3 M (dirichletTerm s))
          atTop (nhds 0) := by
      simpa [hchart] using hlimit
    simpa [NativeCarryLogWaveBoundaryCloses,
      nativeCarryLogWaveIntegerSample, s] using hzeroLimit

/-- Exact requested equivalence at the level of the fixed interior equation and
fixed bracket boundary condition. -/
theorem nativeCarryLogWaveCharacteristic_iff_resonance
    {z : ℂ} (hz : carryComplexTimeParameter z ∈ genuineCriticalStrip) :
    NativeCarryLogWaveCharacteristic z ↔
      IsNativeCarryComplexTimeResonance z := by
  rw [NativeCarryLogWaveCharacteristic]
  constructor
  · rintro ⟨_, hboundary⟩
    exact (nativeCarryLogWaveBoundaryCloses_iff_resonance hz).1 hboundary
  · intro hres
    refine ⟨nativeCarryLogDilationExpression_wave_eq z, ?_⟩
    exact (nativeCarryLogWaveBoundaryCloses_iff_resonance hz).2 hres

end

end CPFormal.Analytic.Cp
