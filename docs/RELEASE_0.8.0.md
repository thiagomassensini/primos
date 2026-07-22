# Checkpoint 0.8.0 — caixas Cp alinhadas com bordo zero

Este checkpoint escolhe uma familia aritmetica concreta para aplicar a
reindexacao ponderada Cp do checkpoint 0.7.0.

## A caixa bracketada

Fixe um primo impar `p` e um natural `M`. Os centros sao

```text
p, 2p, ..., Mp.
```

Em cada centro entram todos os offsets balanceados nao nulos da camera Cp.
Como a camera possui `p-1` offsets, a caixa possui exatamente

```text
M * (p-1)
```

incidencias. A construcao Lean usa um embedding dos pares
`(indice do centro, offset)`; a prova de injetividade impede colisoes entre
centros ou pernas.

## A caixa direta

A caixa de pernas nao e postulada por um intervalo ad hoc. Ela e definida
como a pre-imagem da caixa bracketada pela equivalencia global

```text
inteiro nao multiplo de p  <->  (centro multiplo de p, offset balanceado).
```

Por isso, aplicar a equivalencia de volta recupera exatamente a caixa de
incidencias. O kernel conclui

```text
extras    = vazio
faltantes = vazio.
```

## Igualdade ponderada

Para qualquer anel comutativo, qualquer valor `value(n)` e qualquer funcao de
peso que dependa da profundidade de carry,

```text
sum(pernas da caixa, peso(profundidade efetiva) * value(perna))
  =
sum(incidencias alinhadas, peso(v_p(centro)) * value(centro+offset)).
```

Nao existe termo de bordo nessa caixa finita.

## Endpoints Lean

- `Carry.Cp.alignedIncidence`;
- `Carry.Cp.alignedIncidenceEmbedding`;
- `Carry.Cp.incidenceIndexBox`;
- `Carry.Cp.alignedIncidenceBox`;
- `Carry.Cp.mem_alignedIncidenceBox_iff`;
- `Carry.Cp.card_incidenceIndexBox`;
- `Carry.Cp.card_alignedIncidenceBox`;
- `Carry.Cp.alignedNonmultipleBox`;
- `Carry.Cp.card_alignedNonmultipleBox`;
- `Carry.Cp.incidenceImage_alignedNonmultipleBox`;
- `Carry.Cp.extraIncidences_alignedBox`;
- `Carry.Cp.missingIncidences_alignedBox`;
- `Carry.Cp.weighted_reindex_alignedBox`.

Arquivo principal: `CPFormal/Carry/CpAlignedBox.lean`.

## Evidencia de compilacao

- repositorio privado: `thiagomassensini/primos`;
- branch: `agent/lean-kernel-audit`;
- pull request: `#1` (rascunho);
- commit matematico: `49f8d226f1f9718fb15d76b89c5934f9852e8303`;
- workflow run: `29642943076`;
- job: `88076344500`;
- resultado: auditoria estatica e `lake build --wfail` concluidos com sucesso.

## Alcance exato

Este checkpoint fecha uma igualdade finita e algebrica. Ele nao passa ao
limite `M -> infinito`, nao prova convergencia, nao identifica a soma com zeta
ou funcao L, nao prova equivalencia de zeros e nao constroi ainda um operador
Hilbert--Polya.

O proximo passo e caracterizar a pre-imagem diretamente em termos de limites
e residuos inteiros. Depois disso, a passagem Genuine-first entra na fase
analitica: potencias complexas, majoracao de cauda e convergencia.
