import CPFormal.Analytic.CpNativeGpreTowerNorm

/-!
# Cotas aritmeticas nativas para o lift G_pre

Este modulo continua a construcao concreta da torre nativa. A primeira camada
identifica o perfil de potencia inteiro com a funcao aritmetica canonica.
Nenhuma hipotese espectral ou lei Green entra aqui.
-/

open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius

namespace CPFormal.Analytic.Cp

noncomputable section

open ArithmeticFunction

/-- O perfil inteiro usado por `G_pre` e o cast do perfil aritmetico canonico
`n |-> n^(2*tau)`. -/
theorem nativeGprePowerArithmetic_eq_pow (tau : ℕ) :
    nativeGprePowerArithmetic tau =
      (ArithmeticFunction.pow (2 * tau) : ArithmeticFunction ℤ) := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp [nativeGprePowerArithmetic]
  · simp [nativeGprePowerArithmetic, ArithmeticFunction.pow_apply, hn]

end

end CPFormal.Analytic.Cp
