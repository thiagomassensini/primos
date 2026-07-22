# Checkpoint 0.6.0 — profundidade efetiva do carry Cp

Este checkpoint fecha a ponte entre a bijecao global centro--offset Cp e os
pesos por profundidade de carry.

## Definicao independente

Para uma perna inteira `n` e um primo impar `p`, cada offset balanceado `a` da
carta produz a profundidade candidata

```text
offsetDepth(p,n,a) = padicValInt p (n-a).
```

A profundidade efetiva e o supremo finito sobre a carta inteira:

```text
effectiveDepth(p,n) = sup {offsetDepth(p,n,a) | a em balancedOffsets(p)}.
```

Essa definicao nao usa o centro nem o offset canonico. Portanto a igualdade
abaixo nao e uma calibracao circular.

## Enunciados verificados pelo kernel

Fixe um primo impar `p` e uma perna `n` nao divisivel por `p`.

1. Um offset balanceado `a` satisfaz `p | (n-a)` se, e somente se, `a` e o
   offset canonico determinado pela classe residual de `n`.
2. Todo offset nao canonico possui profundidade zero.
3. A profundidade do offset canonico e a profundidade do centro canonico.
4. O supremo das profundidades de todas as pernas e exatamente a profundidade
   do centro canonico.
5. Se o centro canonico nao e zero, essa profundidade e ao menos um.

Em formulas:

```text
p | (n-a)  <->  a = offsetCanonico(n)

effectiveDepth(p,n)
  = padicValInt p (centerOfNonmultiple(p,n)).
```

## Convencao no centro zero

A `padicValInt` da Mathlib e uma funcao com valores naturais e adota
`padicValInt p 0 = 0`. A igualdade principal continua valida no caso
degenerado `centro = 0`; a afirmacao de profundidade positiva exige e recebe
explicitamente a hipotese `centro != 0`.

## Endpoints Lean

- `Carry.Cp.offsetDepth`;
- `Carry.Cp.effectiveDepth`;
- `Carry.Cp.centerDepth`;
- `Carry.Cp.dvd_sub_iff_eq_offset`;
- `Carry.Cp.offsetDepth_eq_zero_of_ne_offset`;
- `Carry.Cp.offsetDepth_canonical`;
- `Carry.Cp.effectiveDepth_eq_centerDepth`;
- `Carry.Cp.centerDepth_eq_zero_of_center_eq_zero`;
- `Carry.Cp.one_le_centerDepth`.

Arquivo principal: `CPFormal/Carry/CpDepth.lean`.

## Evidencia de compilacao

- repositorio privado: `thiagomassensini/primos`;
- branch: `agent/lean-kernel-audit`;
- pull request: `#1` (rascunho);
- commit matematico: `b24ea3d440198b779d30333df608a4cb0b2c78a0`;
- workflow run: `29640037006`;
- job: `88068948411`;
- resultado: auditoria estatica e `lake build --wfail` concluidos com sucesso.

## Alcance exato

Este checkpoint e aritmetico e finito. Ele justifica transportar um peso que
depende da profundidade da carta para o centro canonico. Ainda nao construiu a
reindexacao ponderada Cp, caixas Cp alinhadas, series infinitas, identidade com
zeta ou funcoes L, equivalencia de zeros, operador Hilbert--Polya autoadjunto
ou prova da RH.

O proximo passo e a reindexacao ponderada Cp com termos de bordo explicitos e,
em seguida, uma familia concreta de caixas alinhadas com bordo vazio.
