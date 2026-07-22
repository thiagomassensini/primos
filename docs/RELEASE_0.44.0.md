# Checkpoint 0.44 — obstrucao do defeito escalar fechado

## Resultado central

O checkpoint 0.43 escreveu o observavel angular comprimido como

```text
ScalarPairing_M = M * GreenPairing_(3M) + ClosedBulkDefect_M.
```

O 0.44 orienta a mesma igualdade pelo defeito:

```text
ClosedBulkDefect_M
  = ScalarPairing_M - M * GreenPairing_(3M).
```

No strip critico, as duas portas angulares possuem limites finitos. Portanto
`ScalarPairing_M` converge sem exigir zero Genuine. Por outro lado, a parte
real do pareamento Green e monotona e permanece acima da primeira aresta,
que e estritamente positiva. O kernel conclui:

```text
Re(ClosedBulkDefect_M) -> -infinity
```

em todo ponto de `genuineCriticalStrip`, ainda sem hipotese de zero.

Mais precisamente, se `E_1(s)` e a parte real positiva do primeiro corte
Green, o kernel prova eventualmente

```text
Re(ClosedBulkDefect_(M+1) / (M+1)) < -E_1(s)/2.
```

Em particular, o defeito normalizado nao converge a zero. A persistencia e
linear, e nao apenas uma divergencia absoluta possivelmente sublinear.

## Reclassificacao rigorosa

O `ClosedBulkDefect` nao e um erro de cauda que possa ser provado pequeno.
Ele e o contratermo linear produzido pela compressao escalar. Num zero
Genuine, a identidade ja certificada

```text
M * GreenPairing_(3M) + ClosedBulkDefect_M -> 0
```

e um cancelamento estrutural entre as duas parcelas, nao uma estimativa
pendente que possa separar a energia Green.

Isso corrige o alvo anunciado ao fim do 0.43: provar que esse defeito nao
cancela `M * Green` e impossivel, pois o ledger mostra que ele faz exatamente
esse cancelamento ate o observavel escalar, que permanece limitado e zera
nos zeros Genuine.

## Abertura local preservando bordo

Antes da sintese escalar, cada bloco angular foi aberto como

```text
canonicalAngularGradientBlock(m,s)
  = realCpSaturatedBracket(3,m,s)
      + positiveDirichletValue(s,3m)
      - positiveDirichletValue(s,3(m+1)).
```

Assim o bloco e literalmente o bracket Genuine — para `p=3`, a segunda
diferenca centrada — mais um cobordo de vertices externos. Esta e a forma
local adequada para construir a proxima porta de bordo sem apagar
proveniencia por uma soma escalar.

## O que foi provado

- a decomposicao local `bloco angular = bracket + cobordo`;
- a forma resolvida exata do defeito fechado;
- a convergencia do pareamento escalar em todo o strip;
- a divergencia `Re(ClosedBulkDefect_M) -> -infinity` em todo o strip;
- uma margem linear normalizada estritamente negativa;
- a impossibilidade de tratar o defeito como residual sublinear ou pequeno.

Nenhum desses resultados usa zero Genuine, equacao funcional, simetria de
zeros, `riemannZeta`, operador Hilbert--Polya ou a propria linha critica.

## Proximo nucleo minimo

O observavel final nao pode ser o produto escalar

```text
conj(Phi_M(s)) * Phi_M(s#),
```

pois essa compressao e precisamente o mecanismo que esconde a energia no
contratermo. A rota direta continua Genuine--Green, mas antes da sintese:

1. construir uma forma de bordo `same-s` a partir do portador TFVD/log-jet
   enriquecido, preservando cada coordenada;
2. manter o lado aritmetico antes do quociente de proveniencia e o endpoint
   depois dele;
3. provar uma identidade finita
   `BoundaryForm = RadialGenuineGreen + MovingEndpoint + ProvenanceDefect`;
4. usar as cotas de cutoff ja formalizadas para o endpoint movel;
5. somente depois formular o gate de fechamento Genuine para a relacao de
   bordo tipada.

Hardy e coercividade entram para dominio, closability e controle de cauda.
Eles nao fornecem injetividade para a sintese escalar.

## Teoremas principais

- `canonicalAngularGradientBlock_eq_bracket_add_coboundary`;
- `finiteCanonicalAngularClosedBulkDefect_eq_scalar_sub_mul_green`;
- `finiteCanonicalAngularScalarPairing_tendsto`;
- `finiteCanonicalAngularClosedBulkDefect_re_tendsto_atBot`;
- `eventually_normalizedClosedBulkDefect_re_lt_neg_half`;
- `normalizedClosedBulkDefect_not_tendsto_zero`.

## Arquivos

- `CPFormal/Analytic/CpFiniteScalarSynthesisClosedDefectObstruction.lean`;
- `CPFormal.lean`;
- `docs/SOURCE_MAP.md`.

## Validacao local

```text
lake build --wfail
```

- elaboracao isolada do novo modulo: **success**;
- auditoria estatica: **success**;
- elaboracao integral pelo kernel: **success**;
- nenhum `sorry`, `admit` ou axioma local.

## Evidencia remota

- commit matematico: `b2b944b448f229cb28203db95bb25956fb407c97`;
- head auditado: `96444421399b9dc21e7332ce92379358b89c0582`;
- workflow run: `29748787146` (`Lean kernel audit`);
- job: `88373763393` (`Build CPFormal`).
