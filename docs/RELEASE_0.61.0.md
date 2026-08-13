# CPFormal v0.61.0 — registro histórico corrigido

## Nota semântica

A publicação original descreveu a rigidez do tilt como “confinamento de zeros
nativos”. Essa linguagem e a definição então usada para zero nativo foram
substituídas.

Na API atual:

```text
zero nativo = fechamento da câmera
equilíbrio quadrático = sigma = 1/2
centro Green = detector do deslocamento sigma - 1/2.
```

Consulte `docs/NATIVE_ZERO_SEMANTICS_CORRECTION.md` para a correção formal.

## Conteúdo matemático preservado

O módulo `CPFormal/Analytic/CpCarryTiltBracket.lean` prova, sem zeta, número
complexo ou hipótese de zero:

- `carryBracket2 f c = f (c - 1) + f (c + 1) - 2 * f c`;
- `carryTilt delta x = x ^ (-delta)`;
- `carryTiltBracket_eq_zero_iff`: a curvatura zera exatamente em
  `delta = 0`;
- `carryTiltBracket_criticalDisplacement_sign_trichotomy`:
  - abaixo de `sigma = 1/2`, a curvatura é negativa;
  - em `sigma = 1/2`, a curvatura é zero;
  - acima de `sigma = 1/2`, a curvatura é positiva.

Esses teoremas caracterizam o equilíbrio do detector de tilt. Eles não dizem
que um zero da câmera fora desse equilíbrio deixa de ser zero.

## Separação da camada zeta

A `v0.61.0` também removeu da superfície ativa dois arquivos-folha que faziam
afirmações sobre `RiemannHypothesis`. Permaneceram duas interfaces analíticas
independentes:

- `CpGenuineRiemannZetaIdentification`, para a identificação da continuação;
- `CpNativeCarryMobiusLogDerivativeGuardrail`, para o circuito aritmético de
  Möbius/von Mangoldt.

Nenhuma delas é fonte do equilíbrio quadrático e nenhuma delas redefine o
predicado de zero nativo.

## Verificação histórica

A tag `v0.61.0` registra o artefato original. O `main` posterior contém a
correção semântica e deve ser validado novamente por `lake build --wfail` e
pelo workflow `Lean kernel audit`.
