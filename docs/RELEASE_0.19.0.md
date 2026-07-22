# Checkpoint 0.19.0 — Green Cp finita e endpoint refletido

Este checkpoint inicia o certificado Green concreto pelo nivel que pode ser
verificado sem qualquer passagem informal ao infinito: blocos completos,
somatorios finitos e endpoints literais.

## Identidade Green finita

Para funcoes `u,v : Nat -> R` em um anel comutativo, o kernel verificou

```text
sum_(n<M) ((u_(n+1)-u_n)*v_(n+1) + u_n*(v_(n+1)-v_n))
  = u_M*v_M-u_0*v_0.
```

O bordo e a diferenca dos endpoints por definicao matematica direta. Ele nao
foi definido como `fluxo-bulk` e, portanto, a identidade nao e tautologica.

## Autovetor de bloco e fluxo

Com

```text
g_s(n) = (n+2)^(-s)-(n+1)^(-s)
B_p g_s(n) = sum_(r<p) [f_s(p(n+1)+r+1)-f_s(p(n+1)+r)],
s# = 1-conj(s),
```

a telescopagem finita fornece exatamente

```text
B_p g_s = p^(-s) g_s.
```

Consequentemente, para todo corte `M`, a forma Green finita satisfaz

```text
W_(p,M)(s)
  = (conj(p^(-s))-p^(-s#)) * E#_M(s),

E#_M(s) = sum_(n<M) conj(g_s(n))*g_(s#)(n).
```

Nao existe termo de erro no bulk de blocos completos. O mesmo modulo tambem
reexporta a ligacao Genuine-first ja certificada: em `Re(s)>1`, os cortes
finitos da carta convergem para

```text
(1-p^(1-s))*genuineContinuation(s).
```

## Endpoint externo refletido

No endpoint positivo `M+1`, a reflexao produz a identidade exata

```text
conj((M+1)^(-s)) * (M+1)^(-(1-conj(s))) = (M+1)^(-1).
```

O kernel aplicou o limite de `1/(M+1)` e verificou que esse endpoint externo
tende a zero para todo `s : Complex`. Portanto essa parte da cauda nao e mais
uma hipotese do futuro certificado.

## Fronteira honesta

Este checkpoint nao afirma que o bordo completo se anula. O endpoint inicial
continua presente e precisa ser identificado/cancelado pelo traco bracketado.
Tambem permanecem abertos:

- retirar a fase comum e escrever o fator radial em funcao de
  `delta = Re(s)-1/2`;
- provar a positividade estrita da parte real da energia refletida em
  `0<Re(s)<1`;
- identificar o fluxo/endpoint interno com a porta da carta bracketada e
  deduzir sua anulacao de um zero de `genuineContinuation`;
- construir uma instancia concreta de `SignedGreenCertificate`;
- qualquer operador Hilbert--Polya autoadjunto ou prova de RH.

## Evidencia de compilacao

- repositorio privado: `thiagomassensini/primos`;
- branch: `agent/lean-kernel-audit`;
- pull request: `#1` (rascunho);
- commit matematico final: `7b1275cf6af93a3c03be53e80f780127b42c7b6c`;
- workflow run: `29670152564`;
- job verde: `88147549171`;
- resultado: auditoria estatica e `lake build --wfail` concluidos com sucesso.

## Endpoints principais

- `Analytic.Cp.sum_range_forwardDifference`;
- `Analytic.Cp.finiteGreenBulk_eq_boundary`;
- `Analytic.Cp.cpBlockGradient_eq_eigenvalue_mul`;
- `Analytic.Cp.finiteCpGreenFlux_eq_eigenvalueDifference_mul_pairing`;
- `Analytic.Cp.finiteChart_dirichlet_tendsto_factor_mul_genuineContinuation`;
- `Analytic.Cp.finiteReflectedOuterEndpoint_eq_inv`;
- `Analytic.Cp.finiteReflectedOuterEndpoint_tendsto_zero`.
