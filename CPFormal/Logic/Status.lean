/-!
# Status epistemico das afirmacoes

Este tipo nao participa das provas matematicas. Ele serve para impedir que
evidencia numerica, prova em papel e prova verificada pelo kernel recebam o
mesmo rotulo no projeto.
-/

namespace CPFormal

inductive EvidenceStatus where
  | vision
  | statementDraft
  | paperArgument
  | numericalEvidence
  | leanStatement
  | kernelChecked
  | openBridge
  deriving Repr, DecidableEq

end CPFormal
