import CPFormal.Analytic.CpConnectedC2Defect
import CPFormal.Analytic.CpNativeGpreJordanBounds
import Mathlib.LinearAlgebra.Prod

/-!
# Guarda C2 conectado para o carrier G_pre nativo

O canal Jordan infinito de `G_pre` e multiplicativo. Logo seu cumulante misto
em duas entradas coprimas e zero: a conectividade C2 nao pode nascer da
instanciacao direta dessa massa.

Ha ainda uma obstrucao de grau. Os carriers e tracos atuais de `G_pre`/TFVD
sao lineares nas coordenadas de aresta, enquanto o defeito Richardson de duas
marginais e o produto bilinear `epsilonP * epsilonQ / 2`. Um readout puramente
linear sobre somente o par de marginais nao pode recuperar esse produto em
todos os estados; o wedge TFVD usado pela porta C2 e justamente bilinear.

Esses fatos apontam para a menor extensao plausivel: uma truncacao comum em
duas escalas e uma coordenada tensorial/quadratica de duas cameras. Nenhuma
ponte Genuine--Green e declarada neste modulo.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

open ArithmeticFunction

/-- Cumulante misto da massa Jordan nativa em duas entradas. -/
def nativeGpreJordanPairConnectedCumulant
    (tau m n : ℕ) : ℤ :=
  nativeGpreJordanArithmetic tau (m * n) -
    nativeGpreJordanArithmetic tau m *
      nativeGpreJordanArithmetic tau n

/-- Como o canal Jordan e multiplicativo, seu cumulante conectado se anula
em todo par coprimo. -/
theorem nativeGpreJordanPairConnectedCumulant_eq_zero_of_coprime
    (tau m n : ℕ) (hcoprime : Nat.Coprime m n) :
    nativeGpreJordanPairConnectedCumulant tau m n = 0 := by
  unfold nativeGpreJordanPairConnectedCumulant
  rw [(isMultiplicative_nativeGpreJordanArithmetic tau).map_mul_of_coprime
    (Nat.coprime_iff_gcd_eq_one.mp hcoprime)]
  ring

/-- Em particular, duas bases primas distintas nao produzem defeito conectado
na massa Jordan infinita atual. -/
theorem nativeGpreJordanPairConnectedCumulant_distinct_primes
    (tau p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    nativeGpreJordanPairConnectedCumulant tau p q = 0 := by
  exact nativeGpreJordanPairConnectedCumulant_eq_zero_of_coprime
    tau p q ((Nat.coprime_primes hp hq).2 hpq)

/-- Nenhum funcional puramente linear somente no par de marginais representa
universalmente o produto conectado. E necessario usar uma forma bilinear, um
lift quadratico/tensorial ou uma coordenada de produto adicionada ao estado. -/
theorem no_linear_pair_readout_realizes_connected_product :
    ¬ ∃ L : (ℝ × ℝ) →ₗ[ℝ] ℝ,
      ∀ epsilonP epsilonQ : ℝ,
        L (epsilonP, epsilonQ) = epsilonP * epsilonQ := by
  rintro ⟨L, hL⟩
  have hsum :=
    L.map_add ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)
  have hone : (1 : ℝ) = 0 := by
    calc
      (1 : ℝ) = L (1, 1) := by
        rw [hL]
        norm_num
      _ = L (((1, 0) : ℝ × ℝ) + ((0, 1) : ℝ × ℝ)) := by
        norm_num
      _ = L (1, 0) + L (0, 1) := hsum
      _ = 0 := by
        rw [hL, hL]
        norm_num
  exact one_ne_zero hone

end

end CPFormal.Analytic.Cp
