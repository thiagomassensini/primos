import CPFormal.Analytic.CpFiniteTfvdAngularGreenIntertwiner

/-!
# Comparacao TFVD log-jet--Green por blocos enriquecidos

O checkpoint anterior reteve as tres arestas do bloco angular e as
transportou ao trio Green canonico. Aqui formamos, antes de qualquer sintese
escalar, o wedge refletido entre as portas angular e log-jet enriquecidas.

O calculo local mostra que esse wedge e um fluxo cruzado entre os dois
vertices consecutivos, multiplicado pelo salto de logaritmo. Esse canal nao
e o mesmo objeto que o wedge Green radial. A diferenca e mantida como um
canal tipado e explicito, coordenada por coordenada.

Um witness canonico em `s = 0` prova que nao existe uma identidade universal
entre os dois canais: o wedge Green e zero, enquanto o wedge log-jet vale
`-log(2)/2` na primeira aresta. O witness e apenas finito e algebrico; ele
nao pertence a faixa critica e nao afirma nada sobre zeros ou limites.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Tres valores de wedge, um para cada residuo de um bloco angular. -/
structure TfvdWedgeTriple where
  first : ℂ
  second : ℂ
  dormant : ℂ

/-- Extensionalidade explicita do trio de wedges. -/
theorem TfvdWedgeTriple.ext
    {x y : TfvdWedgeTriple}
    (hfirst : x.first = y.first)
    (hsecond : x.second = y.second)
    (hdormant : x.dormant = y.dormant) :
    x = y := by
  cases x
  cases y
  simp_all

/-- Soma coordenada a coordenada de dois trios de wedges. -/
def TfvdWedgeTriple.add
    (x y : TfvdWedgeTriple) : TfvdWedgeTriple :=
  {
    first := x.first + y.first
    second := x.second + y.second
    dormant := x.dormant + y.dormant
  }

/-- Wedge refletido entre uma aresta angular e sua aresta log-jet. -/
def reflectedLogJetEdgeWedge
    (phi psi phiSharp psiSharp : ℂ) : ℂ :=
  (starRingEnd ℂ) psi * phiSharp -
    (starRingEnd ℂ) phi * psiSharp

/--
Wedge refletido das quatro portas enriquecidas. As tres arestas sao
retornadas antes do pareamento, portanto a coordenada dormente nao e apagada.
-/
def enrichedTfvdReflectedLogJetWedge
    (kappa omega omegaSharp : ℂ)
    (phi psi phiSharp psiSharp : EnrichedAngularTfvdCoordinate) :
    TfvdWedgeTriple :=
  let phiEdges := enrichedAngularTfvdDecode kappa omega phi
  let psiEdges := enrichedAngularTfvdDecode kappa omega psi
  let phiSharpEdges :=
    enrichedAngularTfvdDecode kappa omegaSharp phiSharp
  let psiSharpEdges :=
    enrichedAngularTfvdDecode kappa omegaSharp psiSharp
  {
    first := reflectedLogJetEdgeWedge
      phiEdges.first psiEdges.first
      phiSharpEdges.first psiSharpEdges.first
    second := reflectedLogJetEdgeWedge
      phiEdges.second psiEdges.second
      phiSharpEdges.second psiSharpEdges.second
    dormant := reflectedLogJetEdgeWedge
      phiEdges.dormant psiEdges.dormant
      phiSharpEdges.dormant psiSharpEdges.dormant
  }

/-- O retorno enriquecido calcula o wedge das tres arestas literais. -/
theorem enrichedTfvdReflectedLogJetWedge_encode
    (block blockSharp : ℕ)
    {kappa omega omegaSharp : ℂ}
    (hkappa : kappa ≠ 0)
    (homega : omega ≠ 0)
    (homegaSharp : omegaSharp ≠ 0)
    (phiFirst phiSecond phiDormant : ℂ)
    (psiFirst psiSecond psiDormant : ℂ)
    (phiSharpFirst phiSharpSecond phiSharpDormant : ℂ)
    (psiSharpFirst psiSharpSecond psiSharpDormant : ℂ) :
    enrichedTfvdReflectedLogJetWedge kappa omega omegaSharp
        (enrichedAngularTfvdEncode block kappa omega
          phiFirst phiSecond phiDormant)
        (enrichedAngularTfvdEncode block kappa omega
          psiFirst psiSecond psiDormant)
        (enrichedAngularTfvdEncode blockSharp kappa omegaSharp
          phiSharpFirst phiSharpSecond phiSharpDormant)
        (enrichedAngularTfvdEncode blockSharp kappa omegaSharp
          psiSharpFirst psiSharpSecond psiSharpDormant) =
      {
        first := reflectedLogJetEdgeWedge
          phiFirst psiFirst phiSharpFirst psiSharpFirst
        second := reflectedLogJetEdgeWedge
          phiSecond psiSecond phiSharpSecond psiSharpSecond
        dormant := reflectedLogJetEdgeWedge
          phiDormant psiDormant phiSharpDormant psiSharpDormant
      } := by
  unfold enrichedTfvdReflectedLogJetWedge
  rw [enrichedAngularTfvdDecode_encode block hkappa homega
      phiFirst phiSecond phiDormant,
    enrichedAngularTfvdDecode_encode block hkappa homega
      psiFirst psiSecond psiDormant,
    enrichedAngularTfvdDecode_encode blockSharp hkappa homegaSharp
      phiSharpFirst phiSharpSecond phiSharpDormant,
    enrichedAngularTfvdDecode_encode blockSharp hkappa homegaSharp
      psiSharpFirst psiSharpSecond psiSharpDormant]

/-- Wedge log-jet canonico de uma unica aresta horizontal. -/
def canonicalReflectedLogJetEdgeWedge (n : ℕ) (s : ℂ) : ℂ :=
  reflectedLogJetEdgeWedge
    (positiveDirichletGradient s n)
    (positiveLogDirichletGradient s n)
    (positiveDirichletGradient (reflectedParameter s) n)
    (positiveLogDirichletGradient (reflectedParameter s) n)

/-- Trio log-jet direto nos indices `3m`, `3m+1` e `3m+2`. -/
def canonicalReflectedLogJetWedgeTriple
    (m : ℕ) (s : ℂ) : TfvdWedgeTriple :=
  {
    first := canonicalReflectedLogJetEdgeWedge (3 * m) s
    second := canonicalReflectedLogJetEdgeWedge (3 * m + 1) s
    dormant := canonicalReflectedLogJetEdgeWedge (3 * m + 2) s
  }

/-- O mesmo trio, agora formado diretamente nas quatro portas TFVD. -/
def canonicalEnrichedTfvdReflectedLogJetWedgeTriple
    (kappa : ℂ) (omega : ℕ → ℂ) (m : ℕ) (s : ℂ) :
    TfvdWedgeTriple :=
  enrichedTfvdReflectedLogJetWedge kappa (omega m) (omega m)
    (canonicalEnrichedAngularTfvdCoordinate kappa omega m s)
    (canonicalEnrichedLogJetTfvdCoordinate kappa omega m s)
    (canonicalEnrichedAngularTfvdCoordinate
      kappa omega m (reflectedParameter s))
    (canonicalEnrichedLogJetTfvdCoordinate
      kappa omega m (reflectedParameter s))

/--
O wedge nas portas enriquecidas preserva exatamente os tres residuos do
bloco, sem sintese escalar e sem termo off-diagonal.
-/
theorem canonicalEnrichedTfvdReflectedLogJetWedgeTriple_eq_canonical
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (m : ℕ) (homega : omega m ≠ 0) (s : ℂ) :
    canonicalEnrichedTfvdReflectedLogJetWedgeTriple
        kappa omega m s =
      canonicalReflectedLogJetWedgeTriple m s := by
  unfold canonicalEnrichedTfvdReflectedLogJetWedgeTriple
    canonicalEnrichedAngularTfvdCoordinate
    canonicalEnrichedLogJetTfvdCoordinate
    canonicalReflectedLogJetWedgeTriple
    canonicalReflectedLogJetEdgeWedge
  exact enrichedTfvdReflectedLogJetWedge_encode
    m m hkappa homega homega
    (positiveDirichletGradient s (3 * m))
    (positiveDirichletGradient s (3 * m + 1))
    (positiveDirichletGradient s (3 * m + 2))
    (positiveLogDirichletGradient s (3 * m))
    (positiveLogDirichletGradient s (3 * m + 1))
    (positiveLogDirichletGradient s (3 * m + 2))
    (positiveDirichletGradient (reflectedParameter s) (3 * m))
    (positiveDirichletGradient (reflectedParameter s) (3 * m + 1))
    (positiveDirichletGradient (reflectedParameter s) (3 * m + 2))
    (positiveLogDirichletGradient (reflectedParameter s) (3 * m))
    (positiveLogDirichletGradient (reflectedParameter s) (3 * m + 1))
    (positiveLogDirichletGradient (reflectedParameter s) (3 * m + 2))

/-- Salto logaritmico entre os vertices positivos `n+1` e `n+2`. -/
def positiveLogGap (n : ℕ) : ℂ :=
  (Real.log (((n + 2 : ℕ) : ℝ)) : ℂ) -
    (Real.log (((n + 1 : ℕ) : ℝ)) : ℂ)

/--
Canal de vertices independente produzido pelo wedge log-jet. Ele cruza os
dois endpoints consecutivos em vez de aplicar o autovalor radial Cp.
-/
def reflectedLogJetVertexFlux (n : ℕ) (s : ℂ) : ℂ :=
  positiveLogGap n *
    ((starRingEnd ℂ) (positiveDirichletValue s n) *
        positiveDirichletValue (reflectedParameter s) (n + 1) -
      (starRingEnd ℂ) (positiveDirichletValue s (n + 1)) *
        positiveDirichletValue (reflectedParameter s) n)

/--
Formula fechada do wedge log-jet: o calculo elimina os termos diagonais e
deixa somente o fluxo cruzado de vertices vezes o salto de logaritmo.
-/
theorem canonicalReflectedLogJetEdgeWedge_eq_vertexFlux
    (n : ℕ) (s : ℂ) :
    canonicalReflectedLogJetEdgeWedge n s =
      reflectedLogJetVertexFlux n s := by
  unfold canonicalReflectedLogJetEdgeWedge reflectedLogJetEdgeWedge
    reflectedLogJetVertexFlux positiveLogGap
    positiveLogDirichletGradient positiveLogDirichletValue
  simp only [positiveDirichletGradient_eq_value_sub_value,
    map_sub, map_mul, Complex.conj_ofReal]
  ring

/-- Wedge orientado de uma unica coordenada Green canonica. -/
def canonicalOrientedCpGreenEdge
    (p n : ℕ) (s : ℂ) : ℂ :=
  tfvdReflectedGreenWedge tfvdHaarScale 1 1
    (canonicalCpGreenTfvdCoordinate p n s)
    (canonicalCpGreenTfvdCoordinate p n (reflectedParameter s))

/-- Trio dos wedges Green nos mesmos tres residuos do bloco angular. -/
def canonicalCpGreenWedgeTriple
    (p m : ℕ) (s : ℂ) : TfvdWedgeTriple :=
  {
    first := canonicalOrientedCpGreenEdge p (3 * m) s
    second := canonicalOrientedCpGreenEdge p (3 * m + 1) s
    dormant := canonicalOrientedCpGreenEdge p (3 * m + 2) s
  }

/-- O canal de defeito local compara dois objetos construidos separadamente. -/
def logJetGreenEdgeDefect
    (p n : ℕ) (s : ℂ) : ℂ :=
  reflectedLogJetVertexFlux n s - canonicalOrientedCpGreenEdge p n s

/-- Trio do canal de defeito, ainda com toda a proveniencia residual. -/
def canonicalLogJetGreenDefectTriple
    (p m : ℕ) (s : ℂ) : TfvdWedgeTriple :=
  {
    first := logJetGreenEdgeDefect p (3 * m) s
    second := logJetGreenEdgeDefect p (3 * m + 1) s
    dormant := logJetGreenEdgeDefect p (3 * m + 2) s
  }

/-- Comparacao exata em uma aresta: log-jet = Green + defeito explicito. -/
theorem canonicalReflectedLogJetEdgeWedge_eq_green_add_defect
    (p n : ℕ) (s : ℂ) :
    canonicalReflectedLogJetEdgeWedge n s =
      canonicalOrientedCpGreenEdge p n s +
        logJetGreenEdgeDefect p n s := by
  rw [canonicalReflectedLogJetEdgeWedge_eq_vertexFlux]
  unfold logJetGreenEdgeDefect
  ring

/-- Comparacao bloco a bloco, preservando inclusive a aresta dormente. -/
theorem canonicalReflectedLogJetWedgeTriple_eq_green_add_defect
    (p m : ℕ) (s : ℂ) :
    canonicalReflectedLogJetWedgeTriple m s =
      TfvdWedgeTriple.add
        (canonicalCpGreenWedgeTriple p m s)
        (canonicalLogJetGreenDefectTriple p m s) := by
  apply TfvdWedgeTriple.ext
  · exact canonicalReflectedLogJetEdgeWedge_eq_green_add_defect
      p (3 * m) s
  · exact canonicalReflectedLogJetEdgeWedge_eq_green_add_defect
      p (3 * m + 1) s
  · exact canonicalReflectedLogJetEdgeWedge_eq_green_add_defect
      p (3 * m + 2) s

/-!
Teorema central do checkpoint: o wedge feito nas portas enriquecidas se
decompoe, antes da sintese, no trio Green canonico mais o trio de defeito.
-/
theorem canonicalEnrichedTfvdReflectedLogJetWedgeTriple_eq_green_add_defect
    (p : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (m : ℕ) (homega : omega m ≠ 0) (s : ℂ) :
    canonicalEnrichedTfvdReflectedLogJetWedgeTriple
        kappa omega m s =
      TfvdWedgeTriple.add
        (canonicalCpGreenWedgeTriple p m s)
        (canonicalLogJetGreenDefectTriple p m s) := by
  rw [canonicalEnrichedTfvdReflectedLogJetWedgeTriple_eq_canonical
    hkappa omega m homega s]
  exact canonicalReflectedLogJetWedgeTriple_eq_green_add_defect p m s

/-- Em `s=0`, a primeira aresta log-jet vale exatamente `-log(2)/2`. -/
theorem canonicalReflectedLogJetEdgeWedge_zero_zero :
    canonicalReflectedLogJetEdgeWedge 0 0 =
      -((Real.log 2 : ℝ) : ℂ) / 2 := by
  norm_num [canonicalReflectedLogJetEdgeWedge,
    reflectedLogJetEdgeWedge, positiveLogDirichletGradient,
    positiveLogDirichletValue, positiveDirichletGradient,
    natDirichletTerm, dirichletTerm, reflectedParameter,
    Complex.cpow_neg_one]

/-- Para `s=0`, toda aresta Green ordinaria e nula. -/
theorem canonicalOrientedCpGreenEdge_zero
    (p n : ℕ) :
    canonicalOrientedCpGreenEdge p n 0 = 0 := by
  unfold canonicalOrientedCpGreenEdge
  rw [tfvdReflectedGreenWedge_canonicalCpGreenCoordinates]
  have hgradient : positiveDirichletGradient (0 : ℂ) n = 0 := by
    simp [positiveDirichletGradient, natDirichletTerm, dirichletTerm]
  have hblock : phaseNormalizedCpBlockGradient p (0 : ℂ) n = 0 := by
    unfold phaseNormalizedCpBlockGradient
    rw [cpBlockGradient_eq_eigenvalue_mul, hgradient]
    ring
  rw [hgradient, hblock]
  simp

/--
Witness canonico da obstrucao: a identificacao direta log-jet = Green falha
ja na primeira aresta. Logo o canal de defeito nao pode ser apagado por uma
identidade algebrica universal.
-/
theorem canonicalReflectedLogJetEdgeWedge_ne_green_at_zero
    (p : ℕ) :
    canonicalReflectedLogJetEdgeWedge 0 0 ≠
      canonicalOrientedCpGreenEdge p 0 0 := by
  rw [canonicalReflectedLogJetEdgeWedge_zero_zero,
    canonicalOrientedCpGreenEdge_zero]
  have hlog : Real.log (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  have hlogComplex : ((Real.log (2 : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hlog
  exact neg_ne_zero.mpr (div_ne_zero hlogComplex (by norm_num))

end

end CPFormal.Analytic.Cp
