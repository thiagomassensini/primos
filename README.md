# CPFormal

Formalizacao limpa, incremental e auditavel da geometria de carry, brackets e
cartas primas, seguindo a ordem **Genuine first**.

## Regra central

O projeto nunca usa `sorry`, `axiom` ou um zero conhecido para fabricar o
operador que deveria explica-lo. Uma afirmacao so recebe o estado
`KERNEL_CHECKED` depois que `lake build` termina sem erros.

## Nucleo ativo

- pares simetricos e segunda diferenca centrada;
- bracket saturado finito e sua aditividade;
- comutacao dos shifts multiplicativos, primeiro esqueleto da planura;
- offsets balanceados da camera Cp;
- lei abstrata finita
  `canal direto - brackets = centros sobreviventes`;
- instancias locais e finitas para C2 e Cp;
- bijecao C2 entre pernas impares e incidencias centro-perna;
- igualdade entre profundidade efetiva da perna e profundidade do centro C2;
- reindexacao ponderada C2 com bordo `extras - faltantes` explicito;
- caixas C2 nos centros `4,8,...,4M` com cobertura exata e bordo vazio;
- identificacao dessas pernas com `3,5,...,4M+1` e cardinalidade `2M`;
- bijecao Cp entre offsets balanceados e residuos nao nulos modulo primo;
- cardinalidade `p-1` da camera balanceada Cp;
- bijecao global Cp entre inteiros nao multiplos de `p` e incidencias
  `(centro multiplo de p, offset balanceado)`;
- existencia e unicidade da decomposicao `n = centro + offset`;
- unicidade da perna balanceada que produz carry em cada carta Cp;
- igualdade entre a maior profundidade das pernas e a profundidade `v_p` do
  centro canonico;
- reindexacao ponderada Cp com bordo `extras - faltantes` explicito e corolario
  de cobertura exata;
- caixas Cp alinhadas nos centros `p,2p,...,Mp`, com todas as `p-1` pernas
  balanceadas de cada centro, cardinalidade `M(p-1)` e bordo vazio;
- peso critico de carry `p^(-k)`, amplitude `p^(-k/2)` e identidade
  `amplitude^2 = massa`, transportados sem bordo pela bijecao Cp;
- massa quadratica do operador de ramo definida pela serie
  `(p-1) * sum_{k>=1} p^(-2 k sigma)`;
- forma fechada da serie e criterio exato, para `sigma > 0`,
  `branchNormSq p sigma = 1 <-> sigma = 1/2`;
- tilt transversal de todas as `p-1` pernas da carta Cp e sua decomposicao
  exata como metade da soma dos brackets dos pares `±a`;
- sinal estrito do tilt, para centro fora da camera: negativo abaixo de
  `sigma=1/2`, nulo em `sigma=1/2` e positivo acima;
- rigidez canonica `tilt = 0 <-> sigma = 1/2` no semiplano `sigma>0`, e
  equivalencia entre tilt nulo e defeito nulo da norma;
- abertura finita da carta Cp: cada bracket e um bloco completo de `p`
  posicoes menos `p` copias do centro;
- ladrilhamento exato do prefixo por blocos:
  `blockPrefix = sum_(1 <= n <= pM+halfRange(p)) f(n)`;
- identidade literal
  `finiteChart = sum_(1 <= n <= pM+halfRange(p)) f(n) - p * centerSum`, antes
  de qualquer limite ou potencia complexa;
- termo complexo principal `n^(-s)` em inteiros positivos e fatoracao finita
  exata
  `p * sum_(m=1)^M (p*m)^(-s) = p^(1-s) * sum_(m=1)^M m^(-s)`;
- carta finita de Dirichlet escrita como prefixo longo menos
  `p^(1-s)` vezes o prefixo curto;
- canal Genuine inicial definido pela propria serie positiva, somabilidade dos
  termos e convergencia dos prefixos verificadas em `Re(s)>1`;
- passagem ao limite da identidade finita, para primo impar e `Re(s)>1`:
  `finiteChart_p,M(s) -> (1-p^(1-s)) * genuineDirichlet(s)`;
- cota quadratica da segunda diferenca por `2*C*r^2` e especializacao
  explicita a `x^(-s)`, com ganho de duas potencias;
- identidade finita, para primo impar,
  `Genuine.Cp.bracket = saturatedBracket`, valida em qualquer anel
  comutativo;
- somabilidade absoluta da serie bracketada em `Re(s)>-1` e passagem ao
  limite dos proprios prefixos `Genuine.Cp.finiteChart` para a carta
  bracketada;
- identificacao por unicidade do limite, no semiplano comum `Re(s)>1`,
  `bracketedDirichletChart = (1-p^(1-s))*genuineDirichlet`;
- majorante uniforme somavel em uma bola canonica ao redor de cada ponto de
  `Re(s)>-1`, com constante e expoente independentes do ponto da bola e da
  profundidade do bloco;
- holomorfia da cauda e da carta bracketada em todo o semiplano `Re(s)>-1`;
- unicidade da continuacao analitica: toda funcao analitica nesse semiplano
  que coincide com o fator Genuine em `Re(s)>1` coincide com a carta
  bracketada em todo o dominio;
- confinamento exato dos zeros do fator Cp: `1-p^(1-s)=0` implica
  `Re(s)=1`, logo o fator nao zera no interior da faixa critica;
- quociente `cpGenuineQuotient = bracketedDirichletChart/cpChartFactor`,
  holomorfo na faixa critica e igual a serie Genuine original em `Re(s)>1`;
- equivalencia, no interior da faixa, entre zero da carta e zero do quociente
  Genuine Cp, mantendo explicita a dependencia na camera prima;
- identidade cruzada holomorfa
  `F_q * bracketedChart_p = F_p * bracketedChart_q` em `Re(s)>-1`, obtida
  pelo principio da identidade antes de qualquer divisao;
- independencia da camera: os quocientes `cpGenuineQuotient p` de quaisquer
  primos impares coincidem no interior da faixa critica;
- representante `genuineContinuation`, holomorfo na faixa, igual a serie
  Genuine original em `Re(s)>1` e independente da carta prima escolhida;
- equivalencia global, na faixa, entre zero de qualquer carta prima impar e
  zero do mesmo `genuineContinuation`;
- criterio Green assinado que transforma um certificado concreto de
  fluxo--energia--bordo numa ponte `zero Genuine -> saturacao do ramo`;
- identidade Green finita com bordo literal, autovetor exato
  `B_p g_s=p^(-s)g_s` e fatoracao exata do fluxo refletido em cortes finitos;
- endpoint externo refletido igual a `1/(M+1)` e portanto nulo no limite;
- certificado Green Cp complexo e concreto em corte finito, com fluxo total,
  energia refletida e bordo fechado `1/(M+1)-1`;
- normalizacao de fase aplicada ao bloco antes do Wronskiano, convertendo os
  autovalores refletidos em escalares reais `p^(-delta)` e `p^delta`;
- fatoracao radial exata
  `p^delta-p^(-delta)=2*delta*cpRadialCofactor(p,delta)`, com cofator
  estritamente positivo para toda base prima;
- identidade Green real assinada em corte finito, com fluxo, energia e bordo
  definidos explicitamente antes da igualdade;
- positividade termo a termo: cada aresta do pareamento refletido possui parte
  real estritamente positiva em `0<Re(s)<1`, uniformemente na altura;
- para todo corte nao vazio, a parte real do pareamento refletido e a energia
  radial Green finita completa sao estritamente positivas;
- na camera canonica `p=3`, a semente da carta bracketada e literalmente o
  endpoint Green interno `1`;
- identidade finita independente
  `rawBoundary-trace_M=outerEndpoint-finiteChart_M`, sem definir o bordo como
  residual da igualdade desejada;
- em todo zero de `genuineContinuation` na faixa critica, o bordo bracketado
  acoplado, complexo e real assinado, converge a zero;
- a anulacao ou o controle limite do fluxo de bulk acoplado permanece uma
  obrigacao aberta, nao uma instancia presumida;
- ledger de afirmacoes, mapa de dependencias e caixa de ideias.

Os modulos projetivo e Hilbert--Polya permanecem preservados em
`CPFormal.ResearchReserve`, mas nao sao importados pelo nucleo ativo.

## Principio Genuine first

1. cancelamento finito literal;
2. bijecao carry entre pernas e centros;
3. pesos por profundidade;
4. passagem a series e controle de cauda;
5. identidade da carta e normalizador;
6. somente depois, zeros e pontes globais.

## Como executar

Com `elan` instalado:

```bash
bash scripts/audit.sh
```

Sem acesso ao compilador, a verificacao que nao imita o kernel e:

```bash
bash scripts/static_audit.sh
```

O projeto esta fixado em Lean/mathlib `v4.32.0`. Consulte `docs/AUDIT.md`
para o estado exato da verificacao pelo kernel neste ambiente.

## Integracao continua

`.github/workflows/lean.yml` executa a auditoria estatica e `lake build
--wfail` num runner oficial do GitHub Actions. Um selo verde desse workflow
permite promover os lemas compilados de `LEAN_STATEMENT` para
`KERNEL_CHECKED`; ele nao promove automaticamente pontes matematicas ainda
marcadas como abertas no ledger.

O checkpoint matematico mais recente do nucleo ativo passou por essa
verificacao no commit `d082847d71a26257045de7fb056403ed0c1d02cf`, workflow
run `29706219224`. A certificacao cobre os imports de `CPFormal.lean`;
`CPFormal.ResearchReserve` permanece fora dela.

## Ordem de leitura

1. `docs/WORKING_AGREEMENT.md`
2. `docs/FORMALIZATION_PLAN.md`
3. `docs/CLAIM_LEDGER.md`
4. `docs/RELEASE_0.23.0.md`
5. `docs/VISION_INBOX.md`
6. `CPFormal/Genuine/FiniteCancellation.lean`
7. `CPFormal/Genuine/C2.lean`
8. `CPFormal/Genuine/Cp.lean`
9. `CPFormal/Carry/C2Adjacent.lean`
10. `CPFormal/Carry/C2Depth.lean`
11. `CPFormal/Carry/C2WeightedReindex.lean`
12. `CPFormal/Carry/C2AlignedBox.lean`
13. `CPFormal/Carry/CpBalancedResidue.lean`
14. `CPFormal/Carry/CpGlobalIncidence.lean`
15. `CPFormal/Carry/CpDepth.lean`
16. `CPFormal/Carry/CpWeightedReindex.lean`
17. `CPFormal/Carry/CpAlignedBox.lean`
18. `CPFormal/Carry/CpBranchWeight.lean`
19. `CPFormal/Analytic/CpBranchNorm.lean`
20. `CPFormal/Analytic/CpTilt.lean`
21. `CPFormal/Analytic/CpTiltRigidity.lean`
22. `CPFormal/Genuine/CpFiniteChart.lean`
23. `CPFormal/Analytic/CpFiniteDirichletChart.lean`
24. `CPFormal/Analytic/CpDirichletLimit.lean`
25. `CPFormal/Analytic/CenteredSecondDifferenceBound.lean`
26. `CPFormal/Analytic/DirichletSecondDifference.lean`
27. `CPFormal/Genuine/CpBracketPairing.lean`
28. `CPFormal/Analytic/CpBracketConvergence.lean`
29. `CPFormal/Analytic/CpBracketHolomorphic.lean`
30. `CPFormal/Analytic/CpGenuineQuotient.lean`
31. `CPFormal/Analytic/CpGenuineCompatibility.lean`
32. `CPFormal/Analytic/CpFiniteGreen.lean`
33. `CPFormal/Analytic/CpReflectedEndpoint.lean`
34. `CPFormal/Analytic/CpFiniteGreenCertificate.lean`
35. `CPFormal/Analytic/CpFiniteGreenRadial.lean`
36. `CPFormal/Analytic/CpFiniteGreenPositivity.lean`
37. `CPFormal/Analytic/CpBracketGreenBoundary.lean`
38. `CPFormal/Analytic/CpGreenBridge.lean`
