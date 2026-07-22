import CPFormal.Analytic.CpGenuineFirstFinalKernelGate

/-!
# Gate final na linguagem da amplitude de carry

A valvula vertical ponderada usa a razao

`q_p = (sqrt p)⁻¹`.

Este modulo identifica esse numero com a raiz da massa quadratica de uma
camada do carry, isto e, com `criticalAmplitude p 1 = p^(-1/2)`. Em seguida
reescreve a ultima inclusao de kernels sem tratar `1/2` como uma coordenada
livre do plano complexo:

```
ker Genuine ⊆ ker Green
  ↔ todo zero Genuine usa a amplitude q_p do carry.
```

A igualdade de amplitudes em uma unica camada ja basta, porque toda a torre e
geometrica. O resultado preserva a distincao logica importante: a valvula
ponderada esta construida e vale para todo estado; a afirmacao aritmetica
final e que um zero da sintese Genuine pertence ao setor de amplitude fixado
pelo carry. Nenhuma instancia dessa afirmacao global e postulada aqui.
-/

open scoped Topology

namespace CPFormal.Analytic.Cp

open CPFormal.Carry.Cp

noncomputable section

/-- A razao usada pela valvula vertical e exatamente a amplitude critica da
primeira camada do carry. -/
theorem primeCarryAmplitudeRatio_eq_criticalAmplitude_one
    (p : ℕ) :
    primeCarryAmplitudeRatio p = criticalAmplitude p 1 := by
  have hpnonneg : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have hratioSq :
      (primeCarryAmplitudeRatio p) ^ 2 = (p : ℝ)⁻¹ := by
    unfold primeCarryAmplitudeRatio
    rw [inv_pow, Real.sq_sqrt hpnonneg]
  have hcriticalSq :
      (criticalAmplitude p 1) ^ 2 = (p : ℝ)⁻¹ := by
    rw [criticalAmplitude_sq_eq_mass]
    simp [criticalMass, Real.rpow_neg_one]
  have hratioNonneg : 0 ≤ primeCarryAmplitudeRatio p :=
    primeCarryAmplitudeRatio_nonneg p
  have hcriticalNonneg : 0 ≤ criticalAmplitude p 1 :=
    criticalAmplitude_nonneg p 1
  nlinarith

/-- Numa base prima, coincidir com a amplitude critica ja na primeira camada
equivale a `sigma = 1/2`. -/
theorem branchAmplitude_one_eq_criticalAmplitude_one_iff
    (p : ℕ) (hp : Nat.Prime p) (sigma : ℝ) :
    branchAmplitude p sigma 1 = criticalAmplitude p 1 ↔
      sigma = (1 : ℝ) / 2 := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast hp.ne_one
  constructor
  · intro hamplitude
    unfold branchAmplitude criticalAmplitude at hamplitude
    have hexponent := (Real.rpow_right_inj hp0 hp1).mp hamplitude
    norm_num at hexponent
    linarith
  · intro hsigma
    subst sigma
    exact branchAmplitude_half p 1

/-- A mesma rigidez escrita diretamente com a razao `q_p` usada no Green,
no bracket, no traco e no retorno verticais. -/
theorem branchAmplitude_one_eq_primeCarryAmplitudeRatio_iff
    (p : ℕ) (hp : Nat.Prime p) (sigma : ℝ) :
    branchAmplitude p sigma 1 = primeCarryAmplitudeRatio p ↔
      sigma = (1 : ℝ) / 2 := by
  rw [primeCarryAmplitudeRatio_eq_criticalAmplitude_one]
  exact branchAmplitude_one_eq_criticalAmplitude_one_iff p hp sigma

/-- Formulacao Genuine-first da obrigacao aritmetica: em todo zero no strip,
a primeira camada usa a raiz da massa quadratica determinada pelo carry. -/
def GenuineZerosMatchPrimeCarryAmplitude (p : ℕ) : Prop :=
  ∀ {s : ℂ}, genuineContinuation s = 0 →
    s ∈ genuineCriticalStrip →
      branchAmplitude p s.re 1 = primeCarryAmplitudeRatio p

/-- Igualar a amplitude do zero ao carry e saturar a norma quadratica do
ramo sao exatamente a mesma obrigacao global. -/
theorem genuineZerosMatchPrimeCarryAmplitude_iff_genuineZeroSaturatesCarry
    (p : ℕ) (hp : Nat.Prime p) :
    GenuineZerosMatchPrimeCarryAmplitude p ↔
      GenuineZeroSaturatesCarry p := by
  constructor
  · intro hmatch s hzero hs
    have hcritical : s.re = (1 : ℝ) / 2 :=
      (branchAmplitude_one_eq_primeCarryAmplitudeRatio_iff
        p hp s.re).mp (hmatch hzero hs)
    exact (branchNormSq_eq_one_iff p hp hs.1).2 hcritical
  · intro hsaturates s hzero hs
    have hcritical : s.re = (1 : ℝ) / 2 :=
      (branchNormSq_eq_one_iff p hp hs.1).1
        (hsaturates hzero hs)
    exact
      (branchAmplitude_one_eq_primeCarryAmplitudeRatio_iff
        p hp s.re).2 hcritical

/-- A colagem final dos operadores limite, agora expressa somente como
compatibilidade entre o zero Genuine e a amplitude intrinseca do carry. -/
theorem orthogonalGenuineKernelIncludedInGreenKernel_iff_carryAmplitude
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    OrthogonalGenuineKernelIncludedInGreenKernel p q ↔
      GenuineZerosMatchPrimeCarryAmplitude p := by
  exact
    (orthogonalGenuineKernelIncludedInGreenKernel_iff_genuineZeroSaturatesCarry
      p q hp hq).trans
        (genuineZerosMatchPrimeCarryAmplitude_iff_genuineZeroSaturatesCarry
          p hp).symm

/-- A forma de bordo--proveniencia e a mesma compatibilidade de amplitude.
O endpoint de cutoff e a passagem ao infinito ja foram eliminados pelos
teoremas importados; nao se acrescenta uma hipotese de bordo nova. -/
theorem genuineZerosMatchPrimeCarryAmplitude_iff_seededTfvdRadialClosure
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) :
    GenuineZerosMatchPrimeCarryAmplitude p ↔
      GenuineZerosCloseSeededTfvdGreenRadialObservable
        p kappa omega := by
  rw [← orthogonalGenuineKernelIncludedInGreenKernel_iff_carryAmplitude
      p q hp hq,
    orthogonalGenuineKernelIncludedInGreenKernel_iff_seededTfvdRadialClosure
      p q hp hq hkappa omega homega]

end

end CPFormal.Analytic.Cp
