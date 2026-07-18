# Checkpoint 0.16.0 — holomorfia da carta Cp bracketada

Este checkpoint fecha no kernel a passagem local-uniforme necessaria para
interpretar a carta bracketada como continuacao analitica no semiplano
`Re(s)>-1`.

## Blocos inteiros na variavel espectral

Para bases reais positivas, `x^(-s)` e diferenciavel em todo `s : Complex`.
Consequentemente, cada par de segunda diferenca, cada bloco saturado e a
semente finita da carta sao funcoes inteiras na variavel espectral.

## Majorante uniforme local

Fixado `z` com `Re(z)>-1`, foi escolhida a bola canonica

```text
radius(z) = (Re(z)+1)/2.
```

Todo ponto `w` dessa bola satisfaz

```text
(Re(z)-1)/2 < Re(w).
```

O kernel verificou simultaneamente:

- uma cota uniforme para `||w(w+1)||` na bola;
- uma constante finita obtida somando os raios da camera Cp;
- a dominacao de cada bloco de profundidade `k` por essa constante vezes
  `(k+1)^(-(Re(z)-1)/2-2)`;
- a somabilidade da sequencia dominante, pois `(Re(z)-1)/2>-1`.

A constante e o expoente dependem apenas do centro `z`, nunca do ponto `w`
da bola nem da profundidade `k`. Essa e a forma local do teste M de
Weierstrass usada na prova.

## Holomorfia e principio da identidade

O criterio de Weierstrass da Mathlib fornece a holomorfia da cauda por
`tsum`. Somando a semente finita, o kernel verificou

```text
AnalyticOnNhd Complex (bracketedDirichletChart p)
  {s | -1 < Re(s)}.
```

O semiplano foi provado convexo e preconexo. Assim, para primo impar, toda
funcao `F` analitica nesse dominio que satisfaz

```text
F(s) = (1-p^(1-s))*genuineDirichlet(s)    quando Re(s)>1
```

coincide com `bracketedDirichletChart p` em todo `Re(s)>-1`.

O enunciado nao presume que a expressao totalizada do lado direito ja seja
holomorfa fora de `Re(s)>1`; ele caracteriza honestamente qualquer candidata
analitica `F` e prova sua unicidade.

## Fronteira honesta

A formalizacao usa bolas locais, que sao suficientes para holomorfia. Nao foi
exportado um corolario separado quantificando sobre todo compacto.

Este checkpoint ainda nao:

- identifica `genuineDirichlet` com `riemannZeta` da Mathlib;
- prova que `1-p^(1-s)` nao zera no interior do critical strip;
- deriva equivalencia ou multiplicidade de zeros;
- constroi um certificado Green concreto;
- constroi um operador Hilbert--Polya autoadjunto;
- prova RH.

## Evidencia de compilacao

- repositorio privado: `thiagomassensini/primos`;
- branch: `agent/lean-kernel-audit`;
- pull request: `#1` (rascunho);
- commit matematico: `da0585ced6f3922da6b32d57b54f169910357ca7`;
- workflow run: `29665212572`;
- job verde: `88134403089`;
- resultado: auditoria estatica e `lake build --wfail` concluidos com sucesso.

## Endpoints principais

- `Analytic.Cp.norm_realCpSaturatedBracket_le_local`;
- `Analytic.Cp.summable_localCpBracketMajorant`;
- `Analytic.Cp.differentiableOn_tsum_realCpSaturatedBracket`;
- `Analytic.Cp.analyticOnNhd_bracketedDirichletChart`;
- `Analytic.Cp.isPreconnected_bracketHalfPlane`;
- `Analytic.Cp.bracketedDirichletChart_unique_analytic_continuation`.
