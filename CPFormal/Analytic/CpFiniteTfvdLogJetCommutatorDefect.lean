import CPFormal.Analytic.CpFiniteTfvdLogJetGreenComparison
import CPFormal.Analytic.CpFiniteLogJetCommutator

/-!
# Wedge refletido do comutador log-jet e comparacao com o defeito

O checkpoint anterior provou, antes de qualquer pareamento,

`[B_p, log](s,n) = log(p) * p^(-s) * G_s(n)`.

Este arquivo forma agora o wedge refletido desse comutador com o gradiente
horizontal. As tres proveniencias `3m`, `3m+1` e `3m+2` sao preservadas pela
porta TFVD enriquecida ate depois do pareamento.

O resultado e rigido: o wedge do comutador e `-log(p)` vezes o wedge Green.
Logo ele vive inteiramente na direcao Green e nao pode, por si so, recuperar
o canal cruzado de vertices presente no defeito do checkpoint 0.30.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Multiplicacao coordenada a coordenada de um trio de wedges. -/
def TfvdWedgeTriple.scale (c : ℂ) (x : TfvdWedgeTriple) : TfvdWedgeTriple :=
  {
    first := c * x.first
    second := c * x.second
    dormant := c * x.dormant
  }

/--
Wedge de uma aresta entre o gradiente horizontal e o comutador log-jet
normalizado em fase, na mesma orientacao usada pelo wedge log-jet do 0.30.
-/
def canonicalReflectedCpLogJetCommutatorWedge
    (p n : ℕ) (s : ℂ) : ℂ :=
  reflectedLogJetEdgeWedge
    (positiveDirichletGradient s n)
    (phaseNormalizedCpLogJetCommutator p s n)
    (positiveDirichletGradient (reflectedParameter s) n)
    (phaseNormalizedCpLogJetCommutator
      p (reflectedParameter s) n)

/-- Trio direto do wedge do comutador nos tres residuos canonicos. -/
def canonicalReflectedCpLogJetCommutatorWedgeTriple
    (p m : ℕ) (s : ℂ) : TfvdWedgeTriple :=
  {
    first := canonicalReflectedCpLogJetCommutatorWedge p (3 * m) s
    second := canonicalReflectedCpLogJetCommutatorWedge p (3 * m + 1) s
    dormant := canonicalReflectedCpLogJetCommutatorWedge p (3 * m + 2) s
  }

/--
Porta TFVD enriquecida cujas tres arestas carregam o comutador normalizado.
-/
def canonicalEnrichedCpLogJetCommutatorTfvdCoordinate
    (p : ℕ) (kappa : ℂ) (omega : ℕ → ℂ)
    (m : ℕ) (s : ℂ) : EnrichedAngularTfvdCoordinate :=
  enrichedAngularTfvdEncode m kappa (omega m)
    (phaseNormalizedCpLogJetCommutator p s (3 * m))
    (phaseNormalizedCpLogJetCommutator p s (3 * m + 1))
    (phaseNormalizedCpLogJetCommutator p s (3 * m + 2))

/-- O wedge do comutador formado diretamente nas quatro portas enriquecidas. -/
def canonicalEnrichedTfvdCpLogJetCommutatorWedgeTriple
    (p : ℕ) (kappa : ℂ) (omega : ℕ → ℂ)
    (m : ℕ) (s : ℂ) : TfvdWedgeTriple :=
  enrichedTfvdReflectedLogJetWedge kappa (omega m) (omega m)
    (canonicalEnrichedAngularTfvdCoordinate kappa omega m s)
    (canonicalEnrichedCpLogJetCommutatorTfvdCoordinate
      p kappa omega m s)
    (canonicalEnrichedAngularTfvdCoordinate
      kappa omega m (reflectedParameter s))
    (canonicalEnrichedCpLogJetCommutatorTfvdCoordinate
      p kappa omega m (reflectedParameter s))

/-!
O retorno enriquecido preserva exatamente os tres wedges do comutador, sem
sintese escalar nem descarte da aresta dormente.
-/
theorem canonicalEnrichedTfvdCpLogJetCommutatorWedgeTriple_eq_canonical
    (p : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (m : ℕ) (homega : omega m ≠ 0) (s : ℂ) :
    canonicalEnrichedTfvdCpLogJetCommutatorWedgeTriple
        p kappa omega m s =
      canonicalReflectedCpLogJetCommutatorWedgeTriple p m s := by
  unfold canonicalEnrichedTfvdCpLogJetCommutatorWedgeTriple
    canonicalEnrichedAngularTfvdCoordinate
    canonicalEnrichedCpLogJetCommutatorTfvdCoordinate
    canonicalReflectedCpLogJetCommutatorWedgeTriple
    canonicalReflectedCpLogJetCommutatorWedge
  exact enrichedTfvdReflectedLogJetWedge_encode
    m m hkappa homega homega
    (positiveDirichletGradient s (3 * m))
    (positiveDirichletGradient s (3 * m + 1))
    (positiveDirichletGradient s (3 * m + 2))
    (phaseNormalizedCpLogJetCommutator p s (3 * m))
    (phaseNormalizedCpLogJetCommutator p s (3 * m + 1))
    (phaseNormalizedCpLogJetCommutator p s (3 * m + 2))
    (positiveDirichletGradient (reflectedParameter s) (3 * m))
    (positiveDirichletGradient (reflectedParameter s) (3 * m + 1))
    (positiveDirichletGradient (reflectedParameter s) (3 * m + 2))
    (phaseNormalizedCpLogJetCommutator
      p (reflectedParameter s) (3 * m))
    (phaseNormalizedCpLogJetCommutator
      p (reflectedParameter s) (3 * m + 1))
    (phaseNormalizedCpLogJetCommutator
      p (reflectedParameter s) (3 * m + 2))

/-!
Formula local central. A orientacao do wedge log-jet troca a ordem usada no
Green; por isso aparece o sinal negativo.
-/
theorem canonicalReflectedCpLogJetCommutatorWedge_eq_neg_log_mul_green
    (p : ℕ) (hp : Nat.Prime p) (n : ℕ) (s : ℂ) :
    canonicalReflectedCpLogJetCommutatorWedge p n s =
      -(Real.log (p : ℝ) : ℂ) * canonicalOrientedCpGreenEdge p n s := by
  unfold canonicalReflectedCpLogJetCommutatorWedge
    reflectedLogJetEdgeWedge canonicalOrientedCpGreenEdge
  rw [tfvdReflectedGreenWedge_canonicalCpGreenCoordinates]
  rw [phaseNormalizedCpLogJetCommutator_eq_radial_logScale p hp s n,
    phaseNormalizedCpLogJetCommutator_eq_radial_logScale
      p hp (reflectedParameter s) n,
    phaseNormalizedCpBlockGradient_eq_radial_mul p hp s n,
    phaseNormalizedCpBlockGradient_reflected_eq_radial_mul p hp s n]
  simp only [criticalDisplacement_reflectedParameter, neg_neg,
    map_mul, Complex.conj_ofReal]
  ring

/-- Bloco a bloco, o wedge do comutador e um multiplo escalar do trio Green. -/
theorem canonicalReflectedCpLogJetCommutatorWedgeTriple_eq_scale_green
    (p : ℕ) (hp : Nat.Prime p) (m : ℕ) (s : ℂ) :
    canonicalReflectedCpLogJetCommutatorWedgeTriple p m s =
      TfvdWedgeTriple.scale (-(Real.log (p : ℝ) : ℂ))
        (canonicalCpGreenWedgeTriple p m s) := by
  apply TfvdWedgeTriple.ext
  · exact canonicalReflectedCpLogJetCommutatorWedge_eq_neg_log_mul_green
      p hp (3 * m) s
  · exact canonicalReflectedCpLogJetCommutatorWedge_eq_neg_log_mul_green
      p hp (3 * m + 1) s
  · exact canonicalReflectedCpLogJetCommutatorWedge_eq_neg_log_mul_green
      p hp (3 * m + 2) s

/-!
Versao inteiramente nas portas enriquecidas: as tres proveniencias chegam
ao mesmo multiplo do trio Green.
-/
theorem canonicalEnrichedTfvdCpLogJetCommutatorWedgeTriple_eq_scale_green
    (p : ℕ) (hp : Nat.Prime p)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (m : ℕ) (homega : omega m ≠ 0) (s : ℂ) :
    canonicalEnrichedTfvdCpLogJetCommutatorWedgeTriple
        p kappa omega m s =
      TfvdWedgeTriple.scale (-(Real.log (p : ℝ) : ℂ))
        (canonicalCpGreenWedgeTriple p m s) := by
  rw [canonicalEnrichedTfvdCpLogJetCommutatorWedgeTriple_eq_canonical
    p hkappa omega m homega s]
  exact canonicalReflectedCpLogJetCommutatorWedgeTriple_eq_scale_green
    p hp m s

/-!
Canal que resta depois de separar o wedge do comutador. Ele e definido
diretamente pelo fluxo cruzado de vertices e pelo wedge Green, sem usar o
defeito como entrada.
-/
def logJetCommutatorResidualChannel
    (p n : ℕ) (s : ℂ) : ℂ :=
  reflectedLogJetVertexFlux n s +
    ((Real.log (p : ℝ) : ℂ) - 1) *
      canonicalOrientedCpGreenEdge p n s

/-- Comparacao exata: defeito = wedge do comutador + canal residual explicito. -/
theorem logJetGreenEdgeDefect_eq_commutatorWedge_add_residual
    (p : ℕ) (hp : Nat.Prime p) (n : ℕ) (s : ℂ) :
    logJetGreenEdgeDefect p n s =
      canonicalReflectedCpLogJetCommutatorWedge p n s +
        logJetCommutatorResidualChannel p n s := by
  rw [canonicalReflectedCpLogJetCommutatorWedge_eq_neg_log_mul_green
    p hp n s]
  unfold logJetGreenEdgeDefect logJetCommutatorResidualChannel
  ring

/-- Trio do canal residual, ainda separado por proveniencia. -/
def canonicalLogJetCommutatorResidualTriple
    (p m : ℕ) (s : ℂ) : TfvdWedgeTriple :=
  {
    first := logJetCommutatorResidualChannel p (3 * m) s
    second := logJetCommutatorResidualChannel p (3 * m + 1) s
    dormant := logJetCommutatorResidualChannel p (3 * m + 2) s
  }

/-!
Teorema central de comparacao do checkpoint: o defeito do 0.30 se separa,
residuo por residuo, no wedge do comutador e em um canal adicional explicito.
-/
theorem canonicalLogJetGreenDefectTriple_eq_commutator_add_residual
    (p : ℕ) (hp : Nat.Prime p) (m : ℕ) (s : ℂ) :
    canonicalLogJetGreenDefectTriple p m s =
      TfvdWedgeTriple.add
        (canonicalReflectedCpLogJetCommutatorWedgeTriple p m s)
        (canonicalLogJetCommutatorResidualTriple p m s) := by
  apply TfvdWedgeTriple.ext
  · exact logJetGreenEdgeDefect_eq_commutatorWedge_add_residual
      p hp (3 * m) s
  · exact logJetGreenEdgeDefect_eq_commutatorWedge_add_residual
      p hp (3 * m + 1) s
  · exact logJetGreenEdgeDefect_eq_commutatorWedge_add_residual
      p hp (3 * m + 2) s

/-- A mesma decomposicao usando o wedge retornado pelas portas TFVD. -/
theorem canonicalLogJetGreenDefectTriple_eq_enriched_commutator_add_residual
    (p : ℕ) (hp : Nat.Prime p)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (m : ℕ) (homega : omega m ≠ 0) (s : ℂ) :
    canonicalLogJetGreenDefectTriple p m s =
      TfvdWedgeTriple.add
        (canonicalEnrichedTfvdCpLogJetCommutatorWedgeTriple
          p kappa omega m s)
        (canonicalLogJetCommutatorResidualTriple p m s) := by
  rw [canonicalEnrichedTfvdCpLogJetCommutatorWedgeTriple_eq_canonical
    p hkappa omega m homega s]
  exact canonicalLogJetGreenDefectTriple_eq_commutator_add_residual
    p hp m s

/-- No witness `n=0,s=0`, o wedge do comutador desaparece. -/
theorem canonicalReflectedCpLogJetCommutatorWedge_zero_zero
    (p : ℕ) (hp : Nat.Prime p) :
    canonicalReflectedCpLogJetCommutatorWedge p 0 0 = 0 := by
  rw [canonicalReflectedCpLogJetCommutatorWedge_eq_neg_log_mul_green
    p hp 0 0, canonicalOrientedCpGreenEdge_zero]
  ring

/-- No mesmo witness, o canal residual retém exatamente o fluxo de vertices. -/
theorem logJetCommutatorResidualChannel_zero_zero
    (p : ℕ) :
    logJetCommutatorResidualChannel p 0 0 =
      -((Real.log 2 : ℝ) : ℂ) / 2 := by
  unfold logJetCommutatorResidualChannel
  rw [← canonicalReflectedLogJetEdgeWedge_eq_vertexFlux 0 0,
    canonicalReflectedLogJetEdgeWedge_zero_zero,
    canonicalOrientedCpGreenEdge_zero]
  ring

/-- O defeito do 0.30 possui o mesmo valor nao nulo no witness. -/
theorem logJetGreenEdgeDefect_zero_zero
    (p : ℕ) :
    logJetGreenEdgeDefect p 0 0 =
      -((Real.log 2 : ℝ) : ℂ) / 2 := by
  unfold logJetGreenEdgeDefect
  rw [← canonicalReflectedLogJetEdgeWedge_eq_vertexFlux 0 0,
    canonicalReflectedLogJetEdgeWedge_zero_zero,
    canonicalOrientedCpGreenEdge_zero]
  ring

/-!
Obstrucao kernel-checked: o wedge do comutador nao esgota universalmente o
defeito. No primeiro residuo, ele e zero enquanto o defeito vale `-log(2)/2`.
-/
theorem logJetGreenEdgeDefect_ne_commutatorWedge_at_zero
    (p : ℕ) (hp : Nat.Prime p) :
    logJetGreenEdgeDefect p 0 0 ≠
      canonicalReflectedCpLogJetCommutatorWedge p 0 0 := by
  rw [logJetGreenEdgeDefect_zero_zero,
    canonicalReflectedCpLogJetCommutatorWedge_zero_zero p hp]
  have hlog : Real.log (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  have hlogComplex : ((Real.log (2 : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hlog
  exact div_ne_zero (neg_ne_zero.mpr hlogComplex) (by norm_num)

/-- A obstrucao ja aparece na primeira coordenada do trio `m=0`. -/
theorem canonicalLogJetGreenDefectTriple_ne_commutatorWedgeTriple_at_zero
    (p : ℕ) (hp : Nat.Prime p) :
    canonicalLogJetGreenDefectTriple p 0 0 ≠
      canonicalReflectedCpLogJetCommutatorWedgeTriple p 0 0 := by
  intro h
  have hfirst := congrArg TfvdWedgeTriple.first h
  change logJetGreenEdgeDefect p 0 0 =
    canonicalReflectedCpLogJetCommutatorWedge p 0 0 at hfirst
  exact (logJetGreenEdgeDefect_ne_commutatorWedge_at_zero p hp) hfirst

end

end CPFormal.Analytic.Cp
