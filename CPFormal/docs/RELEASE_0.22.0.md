# Checkpoint 0.22.0 — positividade Green Cp termo a termo

Este checkpoint fecha a obrigacao de sinal do certificado Green finito. A
prova nao usa zeros tabelados, amostragem numerica nem positividade presumida:
ela abre cada aresta refletida e prova uma desigualdade real estrita.

## Aresta refletida

Para o valor positivo `g_s(n)=(n+1)^(-s)`, o somador de uma aresta e

```text
edge(n,s) = conj(g_s(n+1)-g_s(n))
              * (g_(1-conj(s))(n+1)-g_(1-conj(s))(n)).
```

O kernel verificou a expansao exata

```text
edge = 1/(n+2) + 1/(n+1) - crossForward - crossBackward.
```

As normas dos cruzados dependem apenas de `sigma=Re(s)`; a altura imaginaria
permanece arbitraria.

## Margem estrita na faixa

Para `x=n+1`, `y=n+2` e `r=y/x>1`, a soma das normas cruzadas e estritamente
menor que os diagonais quando `0<sigma<1`. O gap reduz-se a

```text
(1-r^(-sigma)) * (1-r^(sigma-1)) > 0.
```

Como `Re(z) <= ||z||`, essa desigualdade implica

```text
Re(edge(n,s)) > 0
```

para toda aresta `n` e todo `s` no interior da faixa critica.

## Pareamento e energia

Somando as arestas, o kernel concluiu, para todo `M>0`,

```text
Re(finiteReflectedGradientPairing(M,s)) > 0.
```

O cofator radial `A_p(delta)` ja era positivo. Portanto, para todo primo `p`,

```text
finiteRadialGreenEnergy(p,M,s) > 0.
```

Esse resultado e finito. Ele nao afirma uma cota inferior uniforme em `M` e
nao realiza automaticamente a passagem ao limite.

## Evidencia de compilacao

- repositorio privado: `thiagomassensini/primos`;
- branch: `agent/lean-kernel-audit`;
- pull request: `#1` (rascunho);
- commit matematico: `1fc3d26f66eff2a4772d6ad5f073b923f6c1156f`;
- workflow run: `29705176557`;
- job verde: `88240845070`;
- resultado: auditoria estatica e `lake build --wfail` concluidos com sucesso.

## Endpoints principais

- `Analytic.Cp.finiteReflectedGradientEdge_eq_diagonal_sub_cross`;
- `Analytic.Cp.norm_reflectedGradientCross_forward`;
- `Analytic.Cp.norm_reflectedGradientCross_backward`;
- `Analytic.Cp.reflected_rpow_cross_sum_lt_inv_sum`;
- `Analytic.Cp.finiteReflectedGradientEdge_re_pos`;
- `Analytic.Cp.finiteReflectedGradientPairing_re_pos`;
- `Analytic.Cp.finiteRadialGreenEnergy_pos`.

## Proximo nucleo minimo

Ligar a porta bracketada de `genuineContinuation` ao fluxo e ao endpoint
interno do certificado finito. Somente depois dessa identidade deve ser feita
a passagem ao limite e construida a instancia concreta de
`SignedGreenCertificate`.

Este checkpoint nao constroi operador Hilbert--Polya e nao prova RH.
