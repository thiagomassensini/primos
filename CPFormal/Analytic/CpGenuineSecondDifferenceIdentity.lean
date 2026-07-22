import CPFormal.Analytic.CpGenuineCompatibility
import CPFormal.Analytic.CpTiltRigidity
import CPFormal.Genuine.C2

/-!
# Identidade de segunda diferenca do Genuine continuado

Este modulo torna publica, numa unica cadeia, a primitiva comum que antes
estava espalhada entre as camadas finita, Genuine e analitica:

* o bracket `C2` e a segunda diferenca centrada de raio `1`;
* o bracket `Cp`, para primo impar, e a soma saturada dessas diferencas;
* o tilt e o mesmo bracket aplicado ao perfil transversal `x^(-delta)`;
* a carta bracketada e a serie dessas diferencas com sua semente;
* `genuineContinuation` e a carta canonica `p = 3` dividida pelo fator
  `1 - 3^(1-s)`.

As igualdades locais sao algebricas e nao usam limites. A leitura da `tsum`
como serie convergente continua restrita a `re(s) > -1`, e a equivalencia de
zeros com o quociente permanece na faixa onde o fator da camera nao zera.

O modulo nao identifica o bracket com o operador de ramo nem com o
Laplaciano Green inteiro: esses objetos possuem carriers, pesos e convencoes
de sinal adicionais.
-/

open scoped BigOperators Topology

namespace CPFormal.Genuine.C2

variable {R : Type*} [CommRing R]

/-- O bracket local `C2` e literalmente a segunda diferenca centrada de
raio `1`. -/
theorem bracket_eq_centeredSecondDifference
    (f : ℤ → R) (center : ℤ) :
    bracket f center =
      CPFormal.centeredSecondDifference f center 1 := by
  simp only [bracket, legSum, CPFormal.centeredSecondDifference,
    nsmul_eq_mul]
  ring

/-- Igualdade extensional dos dois operadores locais `C2`. -/
theorem bracket_operator_eq_centeredSecondDifference :
    (bracket : (ℤ → R) → ℤ → R) =
      fun f center => CPFormal.centeredSecondDifference f center 1 := by
  funext f center
  exact bracket_eq_centeredSecondDifference f center

end CPFormal.Genuine.C2

namespace CPFormal.Genuine.Cp

variable {R : Type*} [CommRing R]

/-- Para primo impar, o operador bracket `Cp` inteiro e a soma saturada das
segundas diferencas centradas de todos os raios admissiveis. -/
theorem bracket_operator_eq_saturatedBracket
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) :
    (bracket p : (ℤ → R) → ℤ → R) =
      CPFormal.saturatedBracket (halfRange p) := by
  funext f center
  exact bracket_eq_saturatedBracket p hp hpodd f center

/-- A menor camera prima impar, `p = 3`, reduz-se a uma unica segunda
diferenca de raio `1`. -/
theorem bracket_three_eq_centeredSecondDifference
    (f : ℤ → R) (center : ℤ) :
    bracket 3 f center =
      CPFormal.centeredSecondDifference f center 1 := by
  simpa [halfRange, CPFormal.saturatedBracket] using
    (bracket_eq_saturatedBracket
      3 (by norm_num) (by norm_num) f center)

/-- Igualdade extensional da camera `p = 3` com o stencil `C2` local. -/
theorem bracket_three_operator_eq_centeredSecondDifference :
    (bracket 3 : (ℤ → R) → ℤ → R) =
      fun f center => CPFormal.centeredSecondDifference f center 1 := by
  funext f center
  exact bracket_three_eq_centeredSecondDifference f center

/-- As cameras locais `C2` e `p = 3` usam exatamente o mesmo stencil de
raio `1`; suas genealogias globais continuam distintas. -/
theorem bracket_three_eq_c2Bracket
    (f : ℤ → R) (center : ℤ) :
    bracket 3 f center = CPFormal.Genuine.C2.bracket f center := by
  rw [bracket_three_eq_centeredSecondDifference,
    CPFormal.Genuine.C2.bracket_eq_centeredSecondDifference]

end CPFormal.Genuine.Cp

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-- Perfil inteiro que transporta somente o deslocamento transversal
`delta = sigma - 1/2`. O centro real fica no carrier, e o bracket inteiro e
aplicado no offset `0`. -/
def transversePowerProfile (delta center : ℝ) (offset : ℤ) : ℝ :=
  (center + (offset : ℝ)) ^ (-delta)

/-- Cada bracket simetrico do tilt e uma segunda diferenca centrada do perfil
transversal. -/
theorem cpPairTilt_eq_centeredSecondDifference
    (delta center : ℝ) (radius : ℤ) :
    cpPairTilt delta center radius =
      CPFormal.centeredSecondDifference
        (transversePowerProfile delta center) 0 radius := by
  simp only [cpPairTilt, transversePowerProfile,
    CPFormal.centeredSecondDifference, nsmul_eq_mul]
  push_cast
  ring

/-- O tilt `Cp` e literalmente o bracket Genuine local aplicado ao perfil
transversal, e nao ao monomio complexo completo `n^(-s)`. -/
theorem cpTilt_eq_genuineBracket
    (p : ℕ) (delta center : ℝ) :
    cpTilt p delta center =
      CPFormal.Genuine.Cp.bracket p
        (transversePowerProfile delta center) 0 := by
  classical
  simp [cpTilt, CPFormal.Genuine.Cp.bracket,
    CPFormal.Genuine.Cp.legSum, transversePowerProfile]

/-- Para primo impar, a mesma identidade escreve o tilt como soma saturada
das segundas diferencas transversais. -/
theorem cpTilt_eq_saturatedBracket
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (delta center : ℝ) :
    cpTilt p delta center =
      CPFormal.saturatedBracket
        (CPFormal.Genuine.Cp.halfRange p)
        (transversePowerProfile delta center) 0 := by
  rw [cpTilt_eq_genuineBracket,
    CPFormal.Genuine.Cp.bracket_eq_saturatedBracket p hp hpodd]

/-- A carta bracketada inteira e a semente seguida da serie universal de
segundas diferencas centradas. Esta igualdade e algebrica; a somabilidade da
serie foi provada separadamente para `re(s) > -1`. -/
theorem bracketedDirichletChart_eq_centeredSecondDifferenceSeries
    (p : ℕ) (s : ℂ) :
    bracketedDirichletChart p s =
      CPFormal.Genuine.Cp.seedSum p (dirichletTerm s) +
        ∑' k : ℕ,
          ∑ radius ∈ Finset.Icc 1 (CPFormal.Genuine.Cp.halfRange p),
            CPFormal.centeredSecondDifference
              (dirichletTerm s)
              (CPFormal.Genuine.Cp.alignedCenter p k)
              (radius : ℤ) := by
  unfold bracketedDirichletChart
  apply congrArg (fun tail : ℂ =>
    CPFormal.Genuine.Cp.seedSum p (dirichletTerm s) + tail)
  apply tsum_congr
  intro k
  simpa [CPFormal.saturatedBracket] using
    (realCpSaturatedBracket_eq_saturatedBracket p k s)

/-- Na camera `p = 3`, a forma geral perde a soma em raios: a semente e
`1` e cada centro carrega somente a segunda diferenca de raio `1`. -/
theorem bracketedDirichletChart_three_eq_one_add_centeredSecondDifferenceSeries
    (s : ℂ) :
    bracketedDirichletChart 3 s =
      1 +
        ∑' k : ℕ,
          CPFormal.centeredSecondDifference
            (dirichletTerm s)
            (CPFormal.Genuine.Cp.alignedCenter 3 k) 1 := by
  rw [bracketedDirichletChart_eq_centeredSecondDifferenceSeries]
  have hseed :
      CPFormal.Genuine.Cp.seedSum 3 (dirichletTerm s) = 1 := by
    norm_num [CPFormal.Genuine.Cp.seedSum,
      CPFormal.Genuine.Cp.halfRange, dirichletTerm]
  rw [hseed]
  apply congrArg (fun tail : ℂ => 1 + tail)
  apply tsum_congr
  intro k
  change
    CPFormal.saturatedBracket
        (CPFormal.Genuine.Cp.halfRange 3)
        (dirichletTerm s)
        (CPFormal.Genuine.Cp.alignedCenter 3 k) =
      CPFormal.centeredSecondDifference
        (dirichletTerm s)
        (CPFormal.Genuine.Cp.alignedCenter 3 k) 1
  exact
    (CPFormal.Genuine.Cp.bracket_eq_saturatedBracket
      3 (by norm_num) (by norm_num)
      (dirichletTerm s)
      (CPFormal.Genuine.Cp.alignedCenter 3 k)).symm.trans
        (CPFormal.Genuine.Cp.bracket_three_eq_centeredSecondDifference
          (dirichletTerm s)
          (CPFormal.Genuine.Cp.alignedCenter 3 k))

/-- O quociente Genuine de qualquer camera e, por definicao comprovada, a
serie de segundas diferencas com semente dividida pelo fator da camera. -/
theorem cpGenuineQuotient_eq_centeredSecondDifferenceSeries
    (p : ℕ) (s : ℂ) :
    cpGenuineQuotient p s =
      (CPFormal.Genuine.Cp.seedSum p (dirichletTerm s) +
        ∑' k : ℕ,
          ∑ radius ∈ Finset.Icc 1 (CPFormal.Genuine.Cp.halfRange p),
            CPFormal.centeredSecondDifference
              (dirichletTerm s)
              (CPFormal.Genuine.Cp.alignedCenter p k)
              (radius : ℤ)) /
        cpChartFactor p s := by
  rw [cpGenuineQuotient,
    bracketedDirichletChart_eq_centeredSecondDifferenceSeries]

/-- Na camera canonica `p = 3`, a semente e `1` e existe somente o raio `1`.
Esta e a formula explicita, sem alias escondido, do objeto que no codigo se
chama `genuineContinuation`. -/
theorem genuineContinuation_eq_centeredSecondDifferenceSeries
    (s : ℂ) :
    genuineContinuation s =
      (1 +
        ∑' k : ℕ,
          CPFormal.centeredSecondDifference
            (dirichletTerm s)
            (CPFormal.Genuine.Cp.alignedCenter 3 k) 1) /
        (1 - (3 : ℂ) ^ (1 - s)) := by
  rw [genuineContinuation, cpGenuineQuotient,
    bracketedDirichletChart_three_eq_one_add_centeredSecondDifferenceSeries,
    cpChartFactor]
  norm_num

/-- Dentro da faixa critica, os cortes finitos construidos pelos mesmos
brackets convergem diretamente ao fator da camera vezes o unico Genuine
continuado. -/
theorem finiteChart_dirichlet_tendsto_factor_mul_genuineContinuation_on_strip
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ =>
        CPFormal.Genuine.Cp.finiteChart p M (dirichletTerm s))
      atTop
      (nhds (cpChartFactor p s * genuineContinuation s)) := by
  rw [← bracketedDirichletChart_eq_cpChartFactor_mul_genuineContinuation
    p hp hpodd hs]
  exact finiteChart_dirichlet_tendsto_bracketedDirichletChart
    p hp hpodd (by linarith [hs.1])

/-- Na faixa critica, um zero Genuine e exatamente o cancelamento da semente
`1` pela serie canonica de segundas diferencas. -/
theorem genuineContinuation_zero_iff_centeredSecondDifferenceSeries_eq_neg_one
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    genuineContinuation s = 0 ↔
      (∑' k : ℕ,
        CPFormal.centeredSecondDifference
          (dirichletTerm s)
          (CPFormal.Genuine.Cp.alignedCenter 3 k) 1) = -1 := by
  rw [← bracketedDirichletChart_zero_iff_genuineContinuation_zero
    3 (by norm_num) (by norm_num) hs]
  rw [bracketedDirichletChart_three_eq_one_add_centeredSecondDifferenceSeries]
  constructor <;> intro h <;> linear_combination h

end

end CPFormal.Analytic.Cp
