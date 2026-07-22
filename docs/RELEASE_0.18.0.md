# Checkpoint 0.18.0 — Genuine canonico independente da camera Cp

Este checkpoint fecha a compatibilidade multibase minima: dentro da faixa
critica, as cartas de todos os primos impares constroem o mesmo objeto
Genuine.

## A passagem segura

Para dois primos impares `p` e `q`, escreva

```text
F_p(s) = 1-p^(1-s)
B_p(s) = bracketedDirichletChart(p,s).
```

Em `Re(s)>1`, os checkpoints anteriores fornecem `B_p=F_p*G` e
`B_q=F_q*G`. Logo

```text
F_q * B_p = F_p * B_q.
```

Os dois lados sao holomorfos em todo `Re(s)>-1`. O kernel aplicou o principio
da identidade nesse semiplano preconexo e prolongou a igualdade cruzada antes
de qualquer divisao. Isso evita criar um buraco artificial na reta onde um
fator pode zerar.

## Cancelamento na faixa critica

No interior `0<Re(s)<1`, os checkpoints anteriores ja provam `F_p != 0` e
`F_q != 0`. Agora o cancelamento e legitimo e fornece

```text
cpGenuineQuotient(p,s) = cpGenuineQuotient(q,s).
```

Foi escolhido `p=3` apenas como representante:

```text
genuineContinuation(s) = cpGenuineQuotient(3,s).
```

O kernel verificou que:

- `genuineContinuation` e holomorfo no interior da faixa critica;
- ele recupera a serie `genuineDirichlet` em `Re(s)>1`;
- todo primo impar produz o mesmo quociente na faixa;
- `B_p(s)=F_p(s)*genuineContinuation(s)` na faixa;
- `B_p(s)=0` se e somente se `genuineContinuation(s)=0` na faixa.

Portanto a compatibilidade nao foi decretada pela definicao de um objeto
global: ela foi deduzida da identidade finita, dos dois limites analiticos e
do principio da identidade.

## Fronteira honesta

Este checkpoint nao:

- identifica `genuineContinuation` com `riemannZeta` da Mathlib;
- prova preservacao de multiplicidades;
- constroi o fluxo e o bordo de um certificado Green concreto;
- constroi um operador Hilbert--Polya autoadjunto;
- prova RH.

O proximo nucleo minimo e Genuine-first: construir o certificado Green em
cortes finitos para este unico escalar Genuine, com bordo explicito, e depois
controlar sua cauda.

## Evidencia de compilacao

- repositorio privado: `thiagomassensini/primos`;
- branch: `agent/lean-kernel-audit`;
- pull request: `#1` (rascunho);
- commit matematico final: `a31645bbf79a2743ab14bfbd0343c30b8b6f510c`;
- workflow run: `29668593622`;
- job verde: `88143422851`;
- resultado: auditoria estatica e `lake build --wfail` concluidos com sucesso.

## Endpoints principais

- `Analytic.Cp.crossNormalizedChart_eq_swap`;
- `Analytic.Cp.cpGenuineQuotient_eq_cpGenuineQuotient`;
- `Analytic.Cp.genuineContinuation_eq_genuineDirichlet`;
- `Analytic.Cp.analyticOnNhd_genuineContinuation_genuineCriticalStrip`;
- `Analytic.Cp.cpGenuineQuotient_eq_genuineContinuation`;
- `Analytic.Cp.bracketedDirichletChart_eq_cpChartFactor_mul_genuineContinuation`;
- `Analytic.Cp.bracketedDirichletChart_zero_iff_genuineContinuation_zero`.
