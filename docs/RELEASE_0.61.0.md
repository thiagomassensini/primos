# CPFormal v0.61.0 — Confinamento nativo por tilt e remoção da Hipótese de Riemann

Esta versão alinha o repositório com a lei **Genuine First**: a teoria nasce do
carry (massa → operador de ramo → amplitude → norma quadrática → bracket →
tilt), o confinamento dos zeros é uma **positividade de curvatura de dois
lados**, e **nenhum teorema fala de Hipótese de Riemann**.

## Novidades

### Tilt nativo: o confinamento como curvatura de dois lados
Novo módulo `CPFormal/Analytic/CpCarryTiltBracket.lean` (sem zeta, sem número
complexo, sem continuação):

* `carryBracket2 f c = f(c-1) + f(c+1) - 2 f(c)` — segunda diferença centrada;
* `carryTilt δ x = x^(-δ)` — o peso de carry inclinado por `δ`;
* `carryTiltBracket δ c` — a curvatura do peso inclinado;
* `carryTiltBracket_eq_zero_iff` — a curvatura anula-se **⇔** `δ = 0`;
* `carryTiltBracket_criticalDisplacement_confines` — a **tricotomia**
  (`δ = σ - 1/2`):
  * `σ < 1/2` ⟹ curvatura `< 0` (peso estritamente côncavo);
  * `σ = 1/2` ⟹ curvatura `= 0`;
  * `1/2 < σ` ⟹ curvatura `> 0` (peso estritamente convexo).

O único expoente com curvatura nula é `1/2`, e a exclusão vale nos **dois lados
por igual** — não por uma simetria `σ ↦ 1-σ`, mas porque o peso curva
definidamente para um lado abaixo da linha e para o outro acima. Confinamento é
positividade de curvatura, não reflexão.

### Substituição da equação funcional pelo tilt
`CPFormal/Analytic/CpGenuineSimpleRootCarryState.lean` deixa de usar a equação
funcional da zeta completa (`completedRiemannZeta_one_sub`) para transportar a
simplicidade refletida. Como nativamente não existe simetria `σ ↦ 1-σ`, a
simplicidade refletida passa a ser o **quarto campo explícito** de
`IsSimpleGenuineZeroInStrip` — uma hipótese visível, não um fato emprestado da
zeta. O arquivo não referencia mais `riemannZeta` / `completedRiemannZeta`.

### Remoção completa da Hipótese de Riemann
Removidos os dois arquivos-folha que faziam afirmações sobre RH:

* `CpMathlibRiemannHypothesisPromotion` (`… ↔ RiemannHypothesis`);
* `CpPrimitiveGenuineZetaZeroSet` (zero Genuine `↔` zero de `riemannZeta`).

O repositório passa a ter **zero** ocorrências de `RiemannHypothesis`. O
resultado nativo `nativeCarryRealPlaneBoundaryClosurePreservesMass_iff_zeroRigidity`
(sem RH) permanece, auto-contido.

## Escopo honesto

Esta versão **não** é a remoção total de zeta. Dois arquivos ainda mencionam a
`riemannZeta` analítica como **ponte de continuação**, não como afirmação de RH:

* `CpGenuineRiemannZetaIdentification` — a continuação analítica do
  `genuineContinuation` é obtida identificando a série de Dirichlet nativa com a
  `riemannZeta` do Mathlib (cuja analiticidade o Mathlib prova). Removê-la
  exigiria re-derivar a continuação analítica do zero.
* `CpNativeCarryMobiusLogDerivativeGuardrail` — a inversão de Möbius/von Mangoldt
  (mostra que a informação dos primos vem da inversão sobre a não-dependência
  dos zeros com os primos); fora do escopo da prova principal.

O confinamento nativo (massa↔amplitude e curvatura↔tilt) e o operador real/
complexo **não dependem** de zeta.

## Verificação

* `lake build --wfail` — verde, sem warnings.
* Núcleo axiom-clean `[propext, Classical.choice, Quot.sound]`, sem `sorry`.
* Testes de regressão Python (rotação real e operador de ramo/tilt) — OK.
* Auditoria estática — imports locais resolvidos; sem `axiom`/`sorry`/`admit`
  locais.

Um laboratório numérico finito não substitui a elaboração pelo kernel Lean; os
mínimos de grade não são prova sobre o limite infinito.
