# Checkpoint 0.17.0 — fator regular e quociente Genuine Cp

Este checkpoint prova no kernel que o fator da carta Cp nao introduz zeros no
interior da faixa critica e constroi o quociente Cp regular correspondente.

## Onde o fator pode zerar

Para primo `p`, a Mathlib fornece a identidade exata

```text
||p^(1-s)|| = p^(1-Re(s)).
```

Como `p>1`:

- se `Re(s)<1`, esse modulo e estritamente maior que um;
- se `Re(s)>1`, esse modulo e estritamente menor que um.

Logo `p^(1-s)` nao pode ser igual a um fora da reta `Re(s)=1`. O kernel
verificou a forma forte

```text
1-p^(1-s)=0  ->  Re(s)=1.
```

Em particular, o fator nao zera no interior `0<Re(s)<1` da faixa critica.

## Quociente Genuine dependente da camera

Foi definido

```text
cpGenuineQuotient(p,s)
  = bracketedDirichletChart(p,s) / (1-p^(1-s)).
```

O kernel verificou que:

- para primo impar e `Re(s)>1`, o quociente coincide com a serie
  `genuineDirichlet` usada desde o inicio da construcao;
- o fator e inteiro na variavel espectral;
- o quociente e holomorfo em `0<Re(s)<1`;
- nessa faixa, a carta e fator vezes quociente;
- zero da carta e equivalente a zero do quociente.

## Fronteira honesta

O nome `cpGenuineQuotient` e o indice `p` sao deliberados. A construcao ainda
nao prova que os quocientes provenientes de duas cameras primas distintas
coincidem dentro da faixa. A igualdade em `Re(s)>1` esta verificada, mas levar
essa igualdade para o outro lado da reta `Re(s)=1` exige um dominio analitico
comum conectado ou uma identificacao independente com uma continuacao
Genuine global.

Este checkpoint tambem nao:

- identifica o quociente com `riemannZeta` da Mathlib;
- prova compatibilidade multibase dos zeros;
- trata multiplicidades;
- constroi um certificado Green concreto;
- constroi um operador Hilbert--Polya autoadjunto;
- prova RH.

## Evidencia de compilacao

- repositorio privado: `thiagomassensini/primos`;
- branch: `agent/lean-kernel-audit`;
- pull request: `#1` (rascunho);
- commit matematico: `26379be9ed40c9196bd85af8bcba6b2808cf2481`;
- workflow run: `29667470934`;
- job verde: `88140361964`;
- resultado: auditoria estatica e `lake build --wfail` concluidos com sucesso.

## Endpoints principais

- `Analytic.Cp.norm_prime_cpow_one_sub`;
- `Analytic.Cp.cpChartFactor_ne_zero_of_re_ne_one`;
- `Analytic.Cp.cpChartFactor_zero_implies_re_eq_one`;
- `Analytic.Cp.cpChartFactor_ne_zero_on_genuineCriticalStrip`;
- `Analytic.Cp.cpGenuineQuotient_eq_genuineDirichlet`;
- `Analytic.Cp.analyticOnNhd_cpGenuineQuotient_genuineCriticalStrip`;
- `Analytic.Cp.bracketedDirichletChart_zero_iff_cpGenuineQuotient_zero`.
