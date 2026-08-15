# CPFormal

Formalizacao limpa, incremental e auditavel da geometria de carry, brackets,
cameras naturais e cartas Genuine. A massa critica e a meia-abscissa nascem
**carry first**; a construcao analitica das cartas continua **Genuine first**.

## Regra central

O projeto nunca usa `sorry`, `axiom` ou um zero conhecido para fabricar o
operador que deveria explica-lo. Uma afirmacao so recebe o estado
`KERNEL_CHECKED` depois que `lake build` termina sem erros.

## Checkpoint v0.62.0 — zero literal e separação do canal Green

Esta release corretiva torna imutável a separação entre três fatos distintos:

```text
carry quadrático -> seleciona o equilíbrio sigma = 1/2
câmera/Genuine   -> registra somente a anulação
centro Green     -> detecta separadamente o deslocamento sigma - 1/2
```

A correção não cria nem exclui zeros. No strip, a câmera real nativa `3` e
`genuineContinuation` continuam realizando literalmente o mesmo teste de
anulação em toda coordenada radial. Se um zero for apresentado fora do
equilíbrio, ele permanece zero e o canal Green adicional permanece não nulo.

A nota de migração e o alcance lógico exato estão em
[`docs/RELEASE_0.62.0.md`](docs/RELEASE_0.62.0.md) e
[`docs/NATIVE_ZERO_SEMANTICS_CORRECTION.md`](docs/NATIVE_ZERO_SEMANTICS_CORRECTION.md).

## Resultado pós-v0.62 — não compensação da cauda de tilt C3

Para todo parâmetro no strip com `Re(s) != 1/2`, o primeiro centro C3
completo domina estritamente toda a cauda dos centros de tilt posteriores.
O bound é uniforme no cutoff e usa a constante explícita

```math
\rho=\frac34\left(\frac65\right)^{3/2},
\qquad \rho^2=\frac{243}{250}<1.
```

Consequentemente, a série cofinal dos blocos de tilt não zera fora da
meia-abscissa. O teorema não usa um zero Genuine e não afirma confinamento.
Ele isola o gate restante com exatidão: num eventual zero off-critical, o
carrier não local mais o seed teria de cancelar esse tilt cofinal não nulo.

A prova, o witness que impede confundir completude com ortogonalidade do
carrier e o alcance lógico exato estão em
[`docs/C3_TILT_TAIL_NONCOMPENSATION.md`](docs/C3_TILT_TAIL_NONCOMPENSATION.md).

O ledger restante também foi fechado sem hipótese de zero:

```math
1+W_\infty(s)+R_\infty(s)
=a_3(s)\,\mathrm{Genuine}(s).
```

Lean prova ainda que `W_infinity` tem projeção estritamente positiva sobre o
primeiro bloco completo. Como `a_3` não zera no strip, a compensação exata
`1 + R_infinity = -W_infinity` é equivalente ao zero Genuine; proibi-la
globalmente é equivalente à não-anulação forte, e não um lema de cutoff mais
fraco. A fórmula, a auditoria de escopo e o alvo geométrico exato restante estão em
[`docs/C3_CARRIER_COMPENSATION_GATE.md`](docs/C3_CARRIER_COMPENSATION_GATE.md).

## Correção semântica do zero nativo

O zero nativo é anulação, sem condição radial embutida:

```lean
def IsNativeCarryRealOperatorZero
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  NativeCarryRealOperatorBoundaryClosesAt camera sigma time
```

As três camadas são distintas e aparecem nessa ordem:

```text
carry quadrático
  -> equilíbrio de massa: sigma = 1/2

camera nativa / Genuine
  -> o mesmo predicado de zero, para todo sigma no strip

centro Green
  -> detecta o tilt sigma - 1/2
```

Em particular, dentro do strip e para a câmera `3`, o Lean prova

```text
IsNativeCarryRealOperatorZero 3 s.re s.im
  <-> genuineContinuation s = 0.
```

Já o operador completado `Genuine ⊕ Green` zera exatamente quando coexistem
o zero nativo/Genuine e o equilíbrio transversal:

```text
genuineGreenCompletedLimitOperator p q s = 0
  <-> IsNativeCarryRealOperatorZero 3 s.re s.im
      and s.re = 1/2.
```

Logo um eventual zero fora do equilíbrio continua sendo zero; quem permanece
não nulo é o canal Green adicional, porque ele denuncia o tilt. A versão
anterior que definia zero como `massCompatible ∧ boundaryCloses` foi removida
da API e está documentada em `docs/NATIVE_ZERO_SEMANTICS_CORRECTION.md`.

## Checkpoint v0.60.0 — fontes finitas explicitas e preservacao completa

`CpNativeGpreFiniteTowerCollapse` constroi, para toda fibra natural de
proveniencia, fontes finitas cujos momentos recuperam exatamente os readouts
`G_pre`. Essa camada e base-neutra: os campos legados chamados `Prime` sao
rotulos naturais, sem certificado de primalidade, e a geometria de carry
continua valida para toda base inteira `b>1`.

`CpNativeGpreTfvdCommutatorTowerSource` especializa a construcao aos
observaveis primos do bulk Green log-jet. Cada aresta analitica `n` ocupa a
celula positiva `p*(n+1)` e o nivel distinto `n+1`; o Lean prova a atividade da
coordenada e a identidade exata entre o momento da fonte de prefixo e o bulk
Green finito. O resultado e camera-a-camera: nao postula um estado comum,
controle uniforme, limite infinito ou confinamento de zeros.

As 22 fontes da sessao interrompida estao preservadas byte a byte em
`docs/recovered/2026-08-01/raw/`, com SHA-256. O manifesto
`docs/POST_V059_PRESERVATION_MANIFEST_2026-08-01.md` registra a reavaliacao dos
PRs e branches posteriores. O escopo publicavel esta em
`docs/RELEASE_0.60.0.md`.

## Checkpoint v0.59.0 — fronteira carry--tilt--Genuine

O carry posicional e sua massa quadratica determinam o deslocamento
`delta = sigma - 1/2`. A convexidade/concavidade estrita do perfil radial
prova, antes de qualquer realizacao em espaco de Hilbert,

```text
cpTiltAtSigma p sigma center = 0  <->  sigma = 1/2.
```

O modulo `CpGenuineCarryTiltFrontier` prova que transferir todo zero Genuine
para esse zero do tilt — ou para o zero equivalente do bulk Green refletido —
e exatamente a afirmacao global de nao anulacao off-critical. Assim a origem
geometrica de `1/2` esta fechada, enquanto a seta global restante continua
tipada e visivel, sem ser introduzida como hipotese disfarçada.

O checkpoint tambem incorpora a reconstrucao TFVD semeada, a conservacao
finita exata da energia de Bessel e a contracao para momentos nativos. A
existencia do estado nativo de tempo fixo e provada equivalente a
`sigma = 1/2`; portanto ela nao e usada para escolher um testemunho a partir
de um zero Genuine bruto. A interface `CpTfvdGpreCollapseInterface` registra
a lei coordenada ainda necessaria sem declarar uma instancia inexistente.

Essa estrutura nao depende de primalidade. Para toda base inteira `b>1`, o
carry e a compatibilidade de massa sao base-neutros; para toda camera natural
nao degenerada `b>=3`, a carta se fatora pelo mesmo
`genuineContinuation`. O modulo `CpNaturalCameraGlobalBlindSpot` empacota a
consequencia: no strip, um zero Genuine e exatamente um ponto cego simultaneo
de todas essas cameras, e todas as suas resultantes finitas convergem a zero.
Ao mesmo tempo, `infiniteReflectedGreenEnergy_pos` mantem a energia Green
refletida estritamente positiva. Isso separa invisibilidade global de perda de
energia, sem afirmar o `GREEN-NATCAM-INTERTWINER` ainda aberto.

Os drafts historicos, inclusive o probe deliberadamente vermelho, foram
auditados. A leitura antiga tratava compatibilidade de massa como parte da
definicao de zero; essa semantica foi corrigida. Massa quadratica, anulacao e
centro Green agora permanecem em predicados distintos. As notas recuperadas
da sessao interrompida foram preservadas em
`docs/recovered/2026-08-01/` como registros de pesquisa, separados dos
certificados do kernel. O escopo publicavel completo esta em
`docs/RELEASE_0.59.0.md`.

## Checkpoint v0.55.0 — sintese estrutural anterior

A formulacao que liga carry posicional, cameras naturais, empacotamento
real--complexo, Green--bracket--retorno, bordo e defeitos explicitos esta em
`docs/UNIVERSAL_CARRY_STRUCTURAL_PERSISTENCE.md`.

Esse documento distingue identidades finitas exatas, continuacoes ja
certificadas, evidencias numericas e pontes ainda abertas. Em particular, ele
registra as formas normais de cameras impares e pares, a identidade da C2
alinhada com o scanner nativo de parametro `4` e raio `1`, e a decomposicao de
cameras compostas impares sem usar primalidade. Essa identidade de
implementacao nao identifica a C2, que tem uma perna por lado, com uma C4
geometrica de duas pernas por lado.
O modulo `CpNaturalCameraAnalyticContinuation` leva essas identidades ao
limite: toda largura `b>=2` produz uma carta convergente e holomorfa em
`Re(s)>-1`; para toda largura nativa nao degenerada `b>=3`, a carta e o fator
de paridade vezes o mesmo `genuineContinuation` na faixa critica. Na linha
`Re(s)=1/2`, todas essas cameras possuem exatamente o mesmo predicado de zero.
A C2 experimental entra pelo parametro nativo `4`, cujo `halfRange` e `1`;
a largura nativa literal `2` permanece separada e degenerada.

## Nucleo ativo

- linguagem certificada de presenca causal por compressao, distinguindo
  ausencia na notacao de ausencia na cadeia operacional;
- torre posicional `carry -> soma -> multiplicacao -> potencia natural` para
  toda base `b>1`, com certificados de decomposicao e iteracao;
- conexao dessa heranca causal com a massa uniforme `b^(-k)`, amplitude
  quadratica e rigidez do expoente `1/2`;
- zero nativo definido somente por fechamento da camera, sem conjuncao com
  compatibilidade de massa;
- identidade exata, no strip, entre o zero da camera real nativa `3` e o zero
  de `genuineContinuation`, para qualquer coordenada radial apresentada;
- centro Green e operador completado mantidos como detectores adicionais do
  deslocamento `sigma-1/2`, sem redefinir o zero nativo/Genuine;
- interface `RestrictedInverseCertificate`, separada da linguagem causal, que
  exige dominios de origem e destino preservados e os dois round-trips;
- certificados restritos `carryBorrowReverseCertificate`,
  `borrowSubtractionCertificate`, `addSubTranslationCertificate`,
  `euclideanSplitCertificate`, `mulDivOnMultiplesCertificate`,
  `powerNthRootOnPerfectPowersCertificate` e
  `basePowerLogOnExactPowersCertificate`;
- leis `floorLog_power_window`, `floorLog_division_step` e
  `repeatedExactDivisionDepth_spec`, mantendo o logaritmo de piso separado da
  profundidade de divisibilidade exata;
- bundle `positionalInverseArithmeticCertificates` para toda base `b>1`,
  limitado aos dominios declarados por cada certificado e sem alegacao de
  inversa global ou de universalidade matematica;
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
- formas normais nativas sem primalidade: prefixo de duas parcelas para toda
  largura impar, prefixo de tres parcelas com canal `D_(b/2)` para toda
  largura par e decomposicao multiplicativa exata de cameras impares
  compostas;
- convergencia absoluta e holomorfia da carta saturada nativa para toda
  largura `b>=2` em `Re(s)>-1`;
- fator unificado `naturalCameraFactor`, identidade cruzada analitica com a
  camera 3 e fatoracao por um unico `genuineContinuation` para toda largura
  nativa `b>=3` na faixa critica;
- nao anulamento de todo fator natural na linha critica e equivalencia entre
  zero da carta e zero Genuine nessa linha, incluindo a C2 alinhada por sua
  igualdade exata com o scanner de parametro `4` e raio `1`;
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
- decomposicao independente do fluxo acoplado como bulk orientado mais bordo
  bracketado, preservando a fatoracao radial exata;
- monotonicidade da parte real do pareamento refletido, com lower positivo ja
  fornecido pelo primeiro corte;
- nos zeros Genuine, equivalencia exata entre anulacao assintotica do fluxo
  acoplado e `Re(s)=1/2`;
- porta angular canonica finita definida independentemente como corrente de
  gradientes com pesos residuais `1,2,0`;
- identidade exata
  `finiteBracketedChart_3,M=finiteAngularTrace_M+(3M+1)^(-s)`;
- para `Re(s)>0`, o bordo angular externo desaparece e o traco converge para
  a carta bracketada; em zeros Genuine na faixa, o traco converge a zero;
- log-jet angular finito construido independentemente sobre o campo
  `log(n+1)*(n+1)^(-s)`, com os mesmos pesos residuais `1,2,0`;
- identidade exata entre a carta log-bracketada, o traco log-jet e um unico
  bordo externo `log(3M+1)*(3M+1)^(-s)`;
- para `Re(s)>0`, esse bordo logaritmico desaparece;
- coordenada TFVD finita enriquecida por indice de bloco, through-flow e
  bracket-flow, com retorno exato das duas arestas;
- leitura TFVD independente que recupera literalmente `Phi_M` e o log-jet
  `Psi_M`, para quaisquer pesos de curvatura nao nulos;
- decomposicao exata do Wronskiano das sinteses escalares em diagonal mais
  interferencia off-diagonal explicita;
- witness kernel-checked mostrando que a interferencia pode ser nao nula, de
  modo que a identificacao da diagonal TFVD com o fluxo Green e sua futura
  lei de anulacao permanecem pontes abertas;
- ledger de afirmacoes, mapa de dependencias e caixa de ideias.

Os modulos projetivo e Hilbert--Polya permanecem preservados em
`CPFormal.ResearchReserve`, mas nao sao importados pelo nucleo ativo.

## Ordem analitica Genuine first

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
verificacao no commit de fonte matematica
`6744f44bf0308af11952ef9e8629357c6be60fcf`, workflow run `30618216161`,
job `91116286122`. A certificacao cobre os imports de `CPFormal.lean`,
incluindo as cameras naturais e o certificado de persistencia estrutural;
`CPFormal.ResearchReserve` permanece fora dela.

O workflow de release da `v0.62.0` repete a auditoria sobre o `main` exato
antes de criar a tag anotada e a GitHub Release. Essa verificacao final do
commit publicado e separada do registro do head matematico acima.

A familia de inversas restritas do checkpoint v0.54.0 esta
`KERNEL_CHECKED` no commit
`8a351323c7476d70e701bed6ab4137d2c5137f2d`, workflow run
`30607820730`, job `91083828864`. Ela usa `RestrictedInverseCertificate` e o
bundle `positionalInverseArithmeticCertificates`; nao cria outro
`CausalCompressionSystem`, nao percorre `CompressionPath` ao contrario e nao
afirma uma inversa global ou uma lei sobre toda a matematica.

## Ordem de leitura

Para uma visao completa deste checkpoint, comece por
`docs/RELEASE_0.62.0.md`,
`docs/NATIVE_ZERO_SEMANTICS_CORRECTION.md`,
`docs/RELEASE_0.60.0.md`,
`docs/POST_V059_PRESERVATION_MANIFEST_2026-08-01.md` e
`docs/ZERO_CONFINEMENT_FRONTIER_AUDIT.md`;
o material recuperado esta indexado em `docs/recovered/2026-08-01/README.md`.
A sintese estrutural anterior permanece em
`docs/UNIVERSAL_CARRY_STRUCTURAL_PERSISTENCE.md`. O resumo da familia causal direta e inversa
permanece em `docs/RESUMO_GERAL_HERANCA_CAUSAL_DO_CARRY.md`, e os limites da
extensao inversa estao registrados em `docs/RELEASE_0.54.0.md`.

Arquivos centrais da fronteira `v0.60.0`:

1. `CPFormal/Analytic/CpNativeCarryRealOperatorZero.lean`
2. `CPFormal/Analytic/CpGenuineNativeRealBoundaryCrosswalk.lean`
3. `CPFormal/Analytic/CpNativeCarryComplexOperatorSameAsReal.lean`
4. `CPFormal/Analytic/CpNativeGenuineGreenCompletedCrosswalk.lean`
5. `CPFormal/Analytic/CpGenuineGreenCompletedOperator.lean`
6. `CPFormal/Analytic/CpTiltRigidity.lean`
7. `CPFormal/Analytic/CpCarryTiltBracket.lean`
8. `docs/NATIVE_ZERO_SEMANTICS_CORRECTION.md`
9. `docs/ZERO_CONFINEMENT_FRONTIER_AUDIT.md`

Ordem historica do nucleo:

1. `docs/WORKING_AGREEMENT.md`
2. `docs/FORMALIZATION_PLAN.md`
3. `docs/CLAIM_LEDGER.md`
4. `docs/RELEASE_0.27.0.md`
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
38. `CPFormal/Analytic/CpBracketGreenFlux.lean`
39. `CPFormal/Analytic/CpAngularPort.lean`
40. `CPFormal/Analytic/CpGreenBridge.lean`
