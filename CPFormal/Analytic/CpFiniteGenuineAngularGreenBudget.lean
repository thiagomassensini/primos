import CPFormal.Analytic.CpFiniteTfvdLogJetCriticalPhaseFan

/-!
# Orcamento angular Genuine-first para o fluxo Green

O checkpoint 0.37 isolou a unica seta ainda ausente:

`zero Genuine -> fechamento do fluxo acoplado`.

Este arquivo nao postula essa seta. Em vez disso, abre a compressao escalar
da porta angular canonica antes de qualquer conclusao sobre a linha critica.
O produto refletido das duas sinteses separa-se em tres parcelas:

1. o pareamento Green diagonal das tres arestas de cada bloco;
2. uma correcao local explicita dentro de cada trio;
3. a interferencia off-diagonal entre blocos distintos.

Se `s` e `s#` sao zeros Genuine, as duas portas escalares tendem a zero e o
orcamento inteiro tambem tende a zero. Uma interface final registra somente
as duas obrigacoes que ainda nao foram provadas: estabilidade refletida dos
zeros e anulacao da correcao nao radial depois do peso radial. Sob esses dois
campos, o kernel constroi `GenuineCarryFluxBridge`.
-/

open scoped BigOperators Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-!
## Produto angular refletido e separacao de registros
-/

/-- Produto de um bloco angular em `s` com outro bloco em `s#`. -/
def canonicalAngularPairingEntry (m n : ℕ) (s : ℂ) : ℂ :=
  (starRingEnd ℂ) (canonicalAngularGradientBlock m s) *
    canonicalAngularGradientBlock n (reflectedParameter s)

/-- Produto formado somente depois de sintetizar as duas portas escalares. -/
def finiteCanonicalAngularScalarPairing (M : ℕ) (s : ℂ) : ℂ :=
  finiteScalarPortWronskian M
    (fun _ ↦ 0)
    (fun m ↦ canonicalAngularGradientBlock m s)
    (fun n ↦ canonicalAngularGradientBlock n (reflectedParameter s))
    (fun _ ↦ 0)

/-- Parte diagonal, ainda escrita com a matriz de proveniencias explicita. -/
def finiteCanonicalAngularPairingDiagonal (M : ℕ) (s : ℂ) : ℂ :=
  finiteDiagonalPortWronskian M
    (fun _ ↦ 0)
    (fun m ↦ canonicalAngularGradientBlock m s)
    (fun n ↦ canonicalAngularGradientBlock n (reflectedParameter s))
    (fun _ ↦ 0)

/-- Interferencia explicita entre blocos angulares distintos. -/
def finiteCanonicalAngularPairingOffDiagonal (M : ℕ) (s : ℂ) : ℂ :=
  finiteOffDiagonalPortWronskian M
    (fun _ ↦ 0)
    (fun m ↦ canonicalAngularGradientBlock m s)
    (fun n ↦ canonicalAngularGradientBlock n (reflectedParameter s))
    (fun _ ↦ 0)

/-- A especializacao escalar e literalmente o produto das duas portas. -/
theorem finiteCanonicalAngularScalarPairing_eq_product
    (M : ℕ) (s : ℂ) :
    finiteCanonicalAngularScalarPairing M s =
      (starRingEnd ℂ) (finiteCanonicalAngularTrace M s) *
        finiteCanonicalAngularTrace M (reflectedParameter s) := by
  simp [finiteCanonicalAngularScalarPairing,
    finiteScalarPortWronskian, finitePortSynthesis,
    finiteCanonicalAngularTrace]

/-- A compressao escalar separa-se exatamente em diagonal e off-diagonal. -/
theorem finiteCanonicalAngularScalarPairing_eq_diagonal_add_offDiagonal
    (M : ℕ) (s : ℂ) :
    finiteCanonicalAngularScalarPairing M s =
      finiteCanonicalAngularPairingDiagonal M s +
        finiteCanonicalAngularPairingOffDiagonal M s := by
  exact finiteScalarPortWronskian_eq_diagonal_add_offDiagonal M
    (fun _ ↦ 0)
    (fun m ↦ canonicalAngularGradientBlock m s)
    (fun n ↦ canonicalAngularGradientBlock n (reflectedParameter s))
    (fun _ ↦ 0)

/-- A matriz diagonal reduz-se ao pareamento do mesmo bloco consigo mesmo. -/
theorem finiteCanonicalAngularPairingDiagonal_eq_sum
    (M : ℕ) (s : ℂ) :
    finiteCanonicalAngularPairingDiagonal M s =
      ∑ m ∈ Finset.range M, canonicalAngularPairingEntry m m s := by
  classical
  simp [finiteCanonicalAngularPairingDiagonal,
    finiteDiagonalPortWronskian, finitePortWedgeEntry,
    canonicalAngularPairingEntry]
  apply Finset.sum_congr rfl
  intro m hm
  rw [if_pos (Finset.mem_range.mp hm)]

/-!
## Correcao local do trio
-/

/--
Correcao local explicita entre o pareamento do bloco angular comprimido e a
soma diagonal das suas tres arestas Green. Os dois primeiros termos sao
cruzados dentro do bloco; o terceiro corrige o peso `2`; o ultimo recoloca a
aresta dormente que tinha peso angular zero.
-/
def canonicalAngularLocalGreenCorrection (m : ℕ) (s : ℂ) : ℂ :=
  2 *
      (starRingEnd ℂ) (positiveDirichletGradient s (3 * m)) *
        positiveDirichletGradient (reflectedParameter s) (3 * m + 1) +
    2 *
      (starRingEnd ℂ) (positiveDirichletGradient s (3 * m + 1)) *
        positiveDirichletGradient (reflectedParameter s) (3 * m) +
    3 *
      (starRingEnd ℂ) (positiveDirichletGradient s (3 * m + 1)) *
        positiveDirichletGradient (reflectedParameter s) (3 * m + 1) -
    (starRingEnd ℂ) (positiveDirichletGradient s (3 * m + 2)) *
      positiveDirichletGradient (reflectedParameter s) (3 * m + 2)

/-- Soma das correcoes locais dos primeiros `M` trios. -/
def finiteCanonicalAngularLocalGreenCorrection
    (M : ℕ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.range M, canonicalAngularLocalGreenCorrection m s

/-- Energia Green diagonal agrupada em trios completos. -/
def finiteCanonicalAngularGreenEnergy (M : ℕ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.range M,
    (finiteReflectedGradientEdge (3 * m) s +
      finiteReflectedGradientEdge (3 * m + 1) s +
      finiteReflectedGradientEdge (3 * m + 2) s)

/-- O produto diagonal de um bloco e energia das tres arestas mais correcao. -/
theorem canonicalAngularPairingEntry_self_eq_greenEnergy_add_correction
    (m : ℕ) (s : ℂ) :
    canonicalAngularPairingEntry m m s =
      (finiteReflectedGradientEdge (3 * m) s +
        finiteReflectedGradientEdge (3 * m + 1) s +
        finiteReflectedGradientEdge (3 * m + 2) s) +
      canonicalAngularLocalGreenCorrection m s := by
  unfold canonicalAngularPairingEntry
    canonicalAngularLocalGreenCorrection finiteReflectedGradientEdge
  rw [canonicalAngularGradientBlock_eq_two_edges,
    canonicalAngularGradientBlock_eq_two_edges]
  simp only [map_neg, map_add, map_mul]
  have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by norm_num
  rw [htwo]
  ring

/-- Agrupar as arestas em trios nao altera o pareamento Green. -/
theorem finiteCanonicalAngularGreenEnergy_eq_pairing
    (M : ℕ) (s : ℂ) :
    finiteCanonicalAngularGreenEnergy M s =
      finiteReflectedGradientPairing (3 * M) s := by
  unfold finiteCanonicalAngularGreenEnergy
    finiteReflectedGradientPairing finiteReflectedGradientEdge
  exact sum_range_threeBlocks_eq_range
    (fun n ↦
      (starRingEnd ℂ) (positiveDirichletGradient s n) *
        positiveDirichletGradient (reflectedParameter s) n) M

/-- A diagonal angular e Green diagonal mais a correcao local dos trios. -/
theorem finiteCanonicalAngularPairingDiagonal_eq_green_add_localCorrection
    (M : ℕ) (s : ℂ) :
    finiteCanonicalAngularPairingDiagonal M s =
      finiteReflectedGradientPairing (3 * M) s +
        finiteCanonicalAngularLocalGreenCorrection M s := by
  rw [finiteCanonicalAngularPairingDiagonal_eq_sum]
  calc
    (∑ m ∈ Finset.range M, canonicalAngularPairingEntry m m s) =
        ∑ m ∈ Finset.range M,
          ((finiteReflectedGradientEdge (3 * m) s +
              finiteReflectedGradientEdge (3 * m + 1) s +
              finiteReflectedGradientEdge (3 * m + 2) s) +
            canonicalAngularLocalGreenCorrection m s) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact canonicalAngularPairingEntry_self_eq_greenEnergy_add_correction m s
    _ = finiteCanonicalAngularGreenEnergy M s +
          finiteCanonicalAngularLocalGreenCorrection M s := by
      rw [Finset.sum_add_distrib]
      rfl
    _ = finiteReflectedGradientPairing (3 * M) s +
          finiteCanonicalAngularLocalGreenCorrection M s := by
      rw [finiteCanonicalAngularGreenEnergy_eq_pairing]

/-- Correcao nao radial total: defeito local mais interferencia entre blocos. -/
def finiteCanonicalAngularGreenCorrection (M : ℕ) (s : ℂ) : ℂ :=
  finiteCanonicalAngularLocalGreenCorrection M s +
    finiteCanonicalAngularPairingOffDiagonal M s

/--
Orcamento finito central: o produto das portas escalares e Green diagonal
mais a correcao nao radial inteira, sem termo escondido.
-/
theorem finiteCanonicalAngularScalarPairing_eq_green_add_correction
    (M : ℕ) (s : ℂ) :
    finiteCanonicalAngularScalarPairing M s =
      finiteReflectedGradientPairing (3 * M) s +
        finiteCanonicalAngularGreenCorrection M s := by
  rw [finiteCanonicalAngularScalarPairing_eq_diagonal_add_offDiagonal,
    finiteCanonicalAngularPairingDiagonal_eq_green_add_localCorrection]
  unfold finiteCanonicalAngularGreenCorrection
  ring

/-!
## Consequencia de um par de zeros Genuine refletidos
-/

/-- A reflexao espectral preserva o interior da faixa critica. -/
theorem reflectedParameter_mem_genuineCriticalStrip
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    reflectedParameter s ∈ genuineCriticalStrip := by
  constructor
  · simpa [reflectedParameter] using (show 0 < 1 - s.re by linarith [hs.2])
  · simpa [reflectedParameter] using (show 1 - s.re < 1 by linarith [hs.1])

/-- Se `s` e `s#` sao zeros Genuine, o produto das portas tende a zero. -/
theorem finiteCanonicalAngularScalarPairing_tendsto_zero_of_genuine_zero_pair
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hzeroSharp : genuineContinuation (reflectedParameter s) = 0) :
    Tendsto (fun M : ℕ ↦ finiteCanonicalAngularScalarPairing M s)
      atTop (nhds 0) := by
  have hphi :=
    finiteCanonicalAngularTrace_tendsto_zero_of_genuine_zero hs hzero
  have hsSharp := reflectedParameter_mem_genuineCriticalStrip hs
  have hphiSharp :=
    finiteCanonicalAngularTrace_tendsto_zero_of_genuine_zero
      hsSharp hzeroSharp
  have hconj :
      Tendsto
        (fun M : ℕ ↦
          (starRingEnd ℂ) (finiteCanonicalAngularTrace M s))
        atTop (nhds 0) := by
    simpa only [Function.comp_apply] using
      (Complex.continuous_conj.tendsto 0).comp hphi
  have hproduct := hconj.mul hphiSharp
  simpa only [finiteCanonicalAngularScalarPairing_eq_product,
    zero_mul] using hproduct

/-- O mesmo par de zeros força Green diagonal mais correcao a tender a zero. -/
theorem finiteCanonicalAngularGreenBudget_tendsto_zero_of_genuine_zero_pair
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hzeroSharp : genuineContinuation (reflectedParameter s) = 0) :
    Tendsto
      (fun M : ℕ ↦
        finiteReflectedGradientPairing (3 * M) s +
          finiteCanonicalAngularGreenCorrection M s)
      atTop (nhds 0) := by
  simpa only [← finiteCanonicalAngularScalarPairing_eq_green_add_correction]
    using
      finiteCanonicalAngularScalarPairing_tendsto_zero_of_genuine_zero_pair
        hs hzero hzeroSharp

/-!
## Reducao final para a ponte carry--Green
-/

/--
As duas obrigacoes analiticas restantes, expostas sem circularidade:

* zeros Genuine sao estaveis pela reflexao espectral;
* a correcao angular nao radial, depois do coeficiente radial, tende a zero.

Nenhuma instancia desta estrutura e declarada aqui.
-/
structure GenuineAngularGreenCancellationBridge (p : ℕ) : Prop where
  reflected_zero :
    ∀ {s : ℂ}, genuineContinuation s = 0 →
      s ∈ genuineCriticalStrip →
      genuineContinuation (reflectedParameter s) = 0
  scaled_correction_closes :
    ∀ {s : ℂ}, genuineContinuation s = 0 →
      s ∈ genuineCriticalStrip →
      Tendsto
        (fun M : ℕ ↦
          ((cpRadialDifference p (criticalDisplacement s.re) : ℝ) : ℂ) *
            finiteCanonicalAngularGreenCorrection M s)
        atTop (nhds 0)

/-- O orcamento angular fecha o deslocamento critico sob as duas obrigacoes. -/
theorem GenuineAngularGreenCancellationBridge.criticalDisplacement_eq_zero
    {p : ℕ} (hp : Nat.Prime p)
    (bridge : GenuineAngularGreenCancellationBridge p)
    {s : ℂ} (hzero : genuineContinuation s = 0)
    (hs : s ∈ genuineCriticalStrip) :
    criticalDisplacement s.re = 0 := by
  let c : ℝ := cpRadialDifference p (criticalDisplacement s.re)
  have hzeroSharp := bridge.reflected_zero hzero hs
  have hbudget :=
    finiteCanonicalAngularGreenBudget_tendsto_zero_of_genuine_zero_pair
      hs hzero hzeroSharp
  have hscaledBudget :
      Tendsto
        (fun M : ℕ ↦
          (c : ℂ) *
            (finiteReflectedGradientPairing (3 * M) s +
              finiteCanonicalAngularGreenCorrection M s))
        atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hbudget
  have hcorrection :
      Tendsto
        (fun M : ℕ ↦
          (c : ℂ) * finiteCanonicalAngularGreenCorrection M s)
        atTop (nhds 0) := by
    simpa [c] using bridge.scaled_correction_closes hzero hs
  have hpairingComplex :
      Tendsto
        (fun M : ℕ ↦
          (c : ℂ) * finiteReflectedGradientPairing (3 * M) s)
        atTop (nhds 0) := by
    have hsub := hscaledBudget.sub hcorrection
    have hfun :
        (fun M : ℕ ↦
          (c : ℂ) * finiteReflectedGradientPairing (3 * M) s) =
        (fun M : ℕ ↦
          (c : ℂ) *
              (finiteReflectedGradientPairing (3 * M) s +
                finiteCanonicalAngularGreenCorrection M s) -
            (c : ℂ) * finiteCanonicalAngularGreenCorrection M s) := by
      funext M
      ring
    rw [hfun]
    simpa using hsub
  have hpairingReal :
      Tendsto
        (fun M : ℕ ↦
          c * (finiteReflectedGradientPairing (3 * M) s).re)
        atTop (nhds 0) := by
    have hre :=
      Complex.continuous_re.continuousAt.tendsto.comp hpairingComplex
    simpa only [Function.comp_apply, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hre
  have hpositive :
      0 < (finiteReflectedGradientPairing 1 s).re :=
    finiteReflectedGradientPairing_re_pos (by norm_num) hs
  have hmonotone := finiteReflectedGradientPairing_re_monotone hs
  have hbound :
      ∀ᶠ M in atTop,
        (finiteReflectedGradientPairing 1 s).re ≤
          (finiteReflectedGradientPairing (3 * M) s).re :=
    eventually_atTop.2 ⟨1, fun M hM ↦ hmonotone (by omega)⟩
  have hc : c = 0 :=
    constant_eq_zero_of_tendsto_mul_of_eventually_pos_lower_bound
      hpositive hbound hpairingReal
  dsimp [c] at hc
  exact (cpRadialDifference_eq_zero_iff
    p hp (criticalDisplacement s.re)).mp hc

/-- As duas obrigacoes angulares constroem a ponte concreta do 0.37. -/
theorem GenuineAngularGreenCancellationBridge.toGenuineCarryFluxBridge
    {p : ℕ} (hp : Nat.Prime p)
    (bridge : GenuineAngularGreenCancellationBridge p) :
    GenuineCarryFluxBridge p := by
  refine ⟨?_⟩
  intro s hzero hs
  have hcritical := bridge.criticalDisplacement_eq_zero hp hzero hs
  exact finiteBracketCoupledCpGreenFlux_tendsto_zero_of_critical
    p hp hs hzero hcritical

end

end CPFormal.Analytic.Cp
