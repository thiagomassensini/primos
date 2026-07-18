# Checkpoint 0.12.0 — ladrilhamento literal da carta Cp

Este checkpoint fecha a ligacao finita minima entre os blocos bracketados e o
prefixo usual dos inteiros positivos.

## Ladrilhamento exato

Para primo impar `p`, qualquer `M` e qualquer funcao com valores num anel
comutativo, o kernel verificou

```text
blockPrefix p M f
  = sum_{1 <= n <= pM+halfRange(p)} f(n).
```

A prova traduz cada bloco completo para seu intervalo inteiro e usa a
adjacencia exata entre blocos consecutivos. Nao ha divisao euclidiana global,
serie infinita ou argumento assintotico.

## Carta finita literal

Combinando o ladrilhamento com o cancelamento bracketado ja certificado:

```text
finiteChart p M f
  = sum_{1 <= n <= pM+halfRange(p)} f(n)
    - p * sum_{k<M} f(p(k+1)).
```

O resultado vale para toda `f`. Portanto uma segunda declaracao que apenas
substituisse `f(n)` por `n^(-s)` nao acrescentaria matematica e foi omitida.

## Proximo nucleo indispensavel

O proximo passo e definir o termo complexo positivo minimo e provar a
fatoracao finita da soma dos centros como `p^(1-s)` vezes o prefixo menor.
Somente depois entram convergencia e controle de cauda.

Continuam abertos a identidade infinita da carta, o certificado Green
concreto, a ponte Genuine--ramo e a RH.

## Evidencia de compilacao

- repositorio privado: `thiagomassensini/primos`;
- branch: `agent/lean-kernel-audit`;
- pull request: `#1` (rascunho);
- commit matematico: `bad4f56825e0d42d0fc628c3a54a46d8503865bf`;
- workflow run: `29649780593`;
- job verde: `88094014871`;
- resultado: auditoria estatica e `lake build --wfail` concluidos com sucesso.

## Endpoints principais

- `Genuine.Cp.centerBlock_eq_sum_Icc`;
- `Genuine.Cp.sum_Icc_split_adjacent`;
- `Genuine.Cp.blockPrefix_succ`;
- `Genuine.Cp.blockPrefix_eq_positiveIntervalSum`;
- `Genuine.Cp.finiteChart_eq_positiveIntervalSum_sub_p_mul_centerSum`.
