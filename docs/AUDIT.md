# Auditoria Genuine-first

## Verificacoes realizadas

- projeto isolado em diretorio novo;
- toolchain e mathlib fixados na mesma versao;
- busca textual por `sorry` e `axiom` prevista antes de cada release;
- cadeia final da RH nao foi declarada como teorema concreto;
- zeros numericos nao aparecem no codigo Lean;
- interfaces condicionais deixam as pontes como campos obrigatorios.
- `scripts/static_audit.sh` verifica imports locais, sintaxe dos scripts e a
  ausencia textual de `sorry`/`axiom` local sem fingir que substitui o kernel.

## Estado do toolchain

- Elan e Lean `v4.32.0` foram instalados isoladamente em `.elan/`;
- a arvore de dependencias da mathlib foi baixada e o manifesto foi criado;
- o sandbox impede `IO.appPath`, usado pelo Lean para localizar o proprio
  executavel;
- por isso o `lake build` falhou antes da elaboracao dos arquivos do projeto,
  com `error: failed to locate application`.

O bloqueio local foi contornado de forma auditavel pelo GitHub Actions, sem
alterar o executavel nem as regras do sandbox.

Primeiro comando obrigatorio num ambiente Lean:

```bash
bash scripts/audit.sh
```

Auditoria estrutural, utilizavel mesmo quando o compilador estiver bloqueado:

```bash
bash scripts/static_audit.sh
```

Se houver erro de elaboracao, o estado continua `LEAN_STATEMENT` ate a correcao
e nova compilacao completa.

## GitHub Actions

O workflow `.github/workflows/lean.yml` usa `leanprover/lean-action@v1` num
runner `ubuntu-latest`, roda primeiro `scripts/static_audit.sh` e depois
`lake build --wfail`. O workflow e uma alternativa limpa ao compilador local
quando o sandbox impede a inicializacao do Lean.

## Certificacao do nucleo ativo

- repositorio privado: `thiagomassensini/primos`;
- pull request de auditoria: `#1`;
- branch: `agent/lean-kernel-audit`;
- commit certificado: `2a29c850389c888c6f1b5bde2dcb899fd261b559`;
- workflow run: `29634840124` (`Lean kernel audit`, run number 9);
- resultado: `success` em `lake build --wfail`;
- Lean: `v4.32.0`;
- mathlib: revisao fixada pelo `lake-manifest.json`.

## Checkpoint ponderado C2

- commit certificado: `0cc016b69419b811cbf12867f46605280ecdf7db`;
- workflow run: `29635654651` (`Lean kernel audit`, run number 17);
- job: `88057413962` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`;
- novo alvo compilado: `CPFormal.Carry.C2WeightedReindex`.

Esse checkpoint certifica a bijecao finita, o transporte do peso de
profundidade e a identidade

```text
direct = expected + extra - missing.
```

Ele nao certifica uma escolha concreta de caixas infinitas, convergencia,
identidade com zeta, equivalencia de zeros ou RH.

## Checkpoint de caixa alinhada C2

- commit certificado: `45b7fe8bb761117609054f0b448c8c11db375b78`;
- workflow run: `29636078858` (`Lean kernel audit`, run number 20);
- job: `88058546887` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`;
- novo alvo compilado: `CPFormal.Carry.C2AlignedBox`.

Esse checkpoint define concretamente os centros `4,8,...,4M`, inclui as duas
pernas de cada centro e prova que a caixa de pernas transportada pela bijecao
recupera exatamente essas incidencias. Portanto os Finsets de extras e de
faltantes sao ambos vazios e a reindexacao ponderada nao possui termo de
bordo.

## Checkpoint de intervalo impar C2

- commit certificado: `b6cdb634a1bbb25eb56709e964d9738e4d001e26`;
- workflow run: `29636657680` (`Lean kernel audit`, run number 25);
- job: `88060082966` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`.

O kernel verificou que a caixa de pernas puxada das incidencias e literalmente
a enumeracao `2k+3`, para `k<2M`. Em particular, seus elementos sao exatamente
os impares de `3` a `4M+1` e sua cardinalidade e `2M`.

## Checkpoint de residuos balanceados Cp

- commit certificado: `211e2a09fa5312c5fb851de9f4a71f05209b0b24`;
- workflow run: `29637023211` (`Lean kernel audit`, run number 27);
- job: `88061047891` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`;
- novo alvo compilado: `CPFormal.Carry.CpBalancedResidue`.

Para primo impar `p`, o kernel verificou a equivalencia entre offsets
balanceados e residuos nao nulos de `ZMod p`. A inversa usa
`ZMod.valMinAbs`, e a camera possui cardinalidade `p-1`.

## Checkpoint da bijecao global Cp

- commit certificado: `e8b9cf7cedf15e7917d7837bb50bb6412d048ccb`;
- workflow run: `29638936254` (`Lean kernel audit`, run number 34);
- job: `88066026811` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`;
- novo alvo compilado: `CPFormal.Carry.CpGlobalIncidence`.

Para primo impar `p`, o kernel verificou que todo inteiro nao divisivel por
`p` possui um unico offset balanceado `a`; o numero `c=n-a` e divisivel por
`p`, e a correspondencia `n <-> (c,a)` e uma equivalencia. Tambem foi
elaborada diretamente a forma existencial unica `∃! (c,a), n=c+a` dentro do
tipo de incidencias.

## Checkpoint da profundidade efetiva Cp

- commit certificado: `b24ea3d440198b779d30333df608a4cb0b2c78a0`;
- workflow run: `29640037006` (`Lean kernel audit`, run number 38);
- job: `88068948411` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`;
- novo alvo compilado: `CPFormal.Carry.CpDepth`.

O kernel verificou que, entre todos os offsets balanceados da carta, apenas o
offset canonico torna `n-a` divisivel por `p`. Os demais termos possuem
`padicValInt` zero, e o supremo finito das profundidades e igual a profundidade
do centro canonico. O caso `centro = 0` segue a convencao explicita da Mathlib
`padicValInt p 0 = 0`; para centro nao nulo, foi provada profundidade ao menos
um.

## Checkpoint da reindexacao ponderada Cp

- commit certificado: `52afc4ffa81f0d62ed732b86de3c4c7f3537284a`;
- workflow run: `29640821068` (`Lean kernel audit`, run number 45);
- job: `88070933888` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`;
- novo alvo compilado: `CPFormal.Carry.CpWeightedReindex`.

O kernel verificou que a bijecao global Cp preserva simultaneamente o valor da
perna e qualquer peso que dependa da profundidade efetiva. Para caixas finitas
arbitrarias, a soma direta e a soma esperada diferem exatamente pelas
incidencias extras menos as faltantes. Quando a imagem da caixa de pernas e a
caixa esperada coincidem, a reindexacao nao possui bordo.

## Checkpoint de caixa alinhada Cp

- commit certificado: `49f8d226f1f9718fb15d76b89c5934f9852e8303`;
- workflow run: `29642943076` (`Lean kernel audit`, run number 57);
- job: `88076344500` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`;
- novo alvo compilado: `CPFormal.Carry.CpAlignedBox`.

Para primo impar `p`, o kernel verificou que os indices dos centros
`p,2p,...,Mp` e de todos os offsets balanceados se injetam nas incidencias sem
colisoes. As caixas de incidencias e de pernas possuem cardinalidade exata
`M(p-1)`. A caixa de pernas e a pre-imagem pela equivalencia global Cp; sua
imagem e, portanto, exatamente a caixa bracketada. Extras e faltantes sao
vazios e a reindexacao ponderada possui bordo zero.

O alvo compilado e `CPFormal.lean`, isto e, o nucleo Genuine-first. O modulo
`CPFormal.ResearchReserve` e seus imports espectrais/projetivos nao foram
promovidos por esse run.

## Checkpoint dos pesos, norma de ramo e tilt Cp

- commit certificado: `aec9140c36ed5274a8eb7e8a919ef86c0971c5e9`;
- workflow run: `29644692098` (`Lean kernel audit`, run number 65);
- job da tentativa verde: `88080985687` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`;
- novos alvos compilados: `CPFormal.Carry.CpBranchWeight`,
  `CPFormal.Analytic.CpBranchNorm` e `CPFormal.Analytic.CpTilt`.

O kernel verificou a identidade amplitude--massa, o transporte dos pesos
`p^(-k)` pela profundidade de carry, a soma geometrica da norma quadratica, o
criterio `norma^2=1 <-> sigma=1/2`, a anulacao critica do tilt Cp e a
implicacao defeito nulo da norma para tilt nulo. A primeira tentativa desse
run falhou antes do Lean por reset de conexao ao instalar Elan; a reexecucao
do mesmo workflow concluiu com sucesso.

A estrutura `GenuineBranchBridge` permanece sem instancia. Portanto esse run
nao prova que um zero Genuine satura a norma; apenas verifica a conclusao
condicional caso essa ponte seja construida.

## Checkpoint da rigidez de sinal do tilt Cp

- commit certificado: `4ed11cfed623a94982a7ba3316f5a290c16fb4c9`;
- workflow run: `29647362054` (`Lean kernel audit`, run number 69);
- job: `88087733439` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`;
- novo alvo compilado: `CPFormal.Analytic.CpTiltRigidity`.

O kernel verificou a invariancia dos offsets balanceados por negacao, a
decomposicao do tilt em brackets simetricos, o sinal estrito de cada bracket
por convexidade/concavidade e a conclusao

```text
cpTiltAtSigma p sigma center = 0  <->  sigma = 1/2
```

para primo impar, `sigma>0` e `center>halfRange(p)`. No mesmo dominio, o zero
do tilt foi identificado com o zero do defeito da norma de ramo. Esse
checkpoint nao fornece uma instancia de `GenuineBranchBridge`.

## Checkpoint da carta finita Cp e do criterio Green

- commit certificado: `e9b8c3d9cd3e13b7085db35b9947743204fcf5b1`;
- workflow run: `29648404437` (`Lean kernel audit`, run number 75);
- job: `88090470740` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`;
- novos alvos compilados: `CPFormal.Genuine.CpFiniteChart` e
  `CPFormal.Analytic.CpGreenBridge`.

O kernel verificou, para qualquer anel comutativo, a decomposicao de cada
bracket Cp como bloco completo menos `p` copias do centro e sua soma nos
primeiros `M` centros. Tambem verificou que uma identidade Green assinada com
energia positiva, fluxo Genuine nulo e bordo nulo produz a ponte para a norma
do ramo.

`SignedGreenCertificate` nao possui uma instancia concreta neste checkpoint.
Em particular, fluxo, cauda, convergencia, identidade infinita da carta e RH
permanecem fora da conclusao certificada.

## Checkpoint do ladrilhamento literal da carta Cp

- commit certificado: `bad4f56825e0d42d0fc628c3a54a46d8503865bf`;
- workflow run: `29649780593` (`Lean kernel audit`, run number 78);
- job: `88094014871` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`;
- alvo compilado ampliado: `CPFormal.Genuine.CpFiniteChart`.

O kernel verificou a traducao de cada bloco para um intervalo inteiro, a
decomposicao de intervalos adjacentes e a inducao que identifica

```text
blockPrefix p M f
  = sum_{1 <= n <= pM+halfRange(p)} f(n).
```

Por substituicao, a carta finita ficou escrita diretamente como esse prefixo
positivo menos `p` vezes a soma dos centros. O enunciado e generico em `f`,
por isso nao se acrescentou uma especializacao redundante em potencias
complexas. Este checkpoint nao certifica fatoracao da soma central,
convergencia, identidade infinita, equivalencia de zeros, certificado Green
concreto ou RH.

## Checkpoint da fatoracao finita de Dirichlet Cp

- commit certificado: `8d941e55af4b1e4e1c6b325b6b07bc90aaa04e8c`;
- workflow run: `29653694412` (`Lean kernel audit`, run number 80);
- job: `88104213909` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`;
- novo alvo compilado: `CPFormal.Analytic.CpFiniteDirichletChart`.

O kernel verificou a multiplicatividade da potencia complexa principal nas
bases naturais nao negativas, a igualdade `p*p^(-s)=p^(1-s)` para primo `p`,
a fatoracao da soma finita dos centros e sua substituicao na carta literal.

O resultado e puramente finito e vale para todo `s : Complex`. Este checkpoint
nao afirma convergencia da serie bracketada, identidade com zeta/Genuine no
limite, continuacao analitica, equivalencia de zeros, certificado Green
concreto ou RH.

## Checkpoint da passagem ao limite Cp em `Re(s)>1`

- commit certificado: `44a539e2c432f88d1bda4670ff3daba1a287819e`;
- workflow run: `29656769332` (`Lean kernel audit`, run number 84);
- job: `88112424965` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`;
- novo alvo compilado: `CPFormal.Analytic.CpDirichletLimit`.

O kernel verificou `Complex.summable_one_div_nat_cpow` sob `Re(s)>1`, o
reindexamento da serie a partir de `n=1`, a convergencia dos prefixos e o fato
de que `pM+halfRange(p)` tende a infinito. Com a identidade finita anterior,
isso produz

```text
finiteChart_p,M(s)
  -> (1-p^(1-s)) * genuineDirichlet(s).
```

O objeto `genuineDirichlet` e a soma da serie positiva definida dentro do
projeto. O checkpoint nao prova que ele coincide, por um teorema separado,
com a zeta de Riemann da Mathlib; tambem nao trata `Re(s)<=1`, continuacao
analitica, equivalencia de zeros, certificado Green concreto ou RH.

## Checkpoint da carta Cp bracketada em `Re(s)>-1`

- commit certificado: `af30c410ed6c68f4f4d9a35a4d88435a592b55c8`;
- workflow run: `29662384450` (`Lean kernel audit`, run number 102);
- job: `88127131010` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`;
- novos alvos compilados: `CPFormal.Analytic.CenteredSecondDifferenceBound`,
  `CPFormal.Analytic.DirichletSecondDifference`,
  `CPFormal.Genuine.CpBracketPairing` e
  `CPFormal.Analytic.CpBracketConvergence`.

O kernel verificou a cota quadratica abstrata da segunda diferenca, as duas
derivadas de `x^(-s)`, o majorante explicito de cada bloco e a somabilidade
absoluta da serie bracketada para `Re(s)>-1`. Para primo impar, tambem
verificou a identidade puramente finita

```text
Genuine.Cp.bracket = saturatedBracket
```

e, portanto, que os proprios prefixos `Genuine.Cp.finiteChart` convergem para
`bracketedDirichletChart`. No semiplano comum `Re(s)>1`, a unicidade do limite
identifica essa carta com `(1-p^(1-s))*genuineDirichlet(s)`.

Este checkpoint prova convergencia absoluta pontual, nao convergencia
localmente uniforme. Assim, ainda nao certifica holomorfia do `tsum`,
continuacao analitica pelo teorema de identidade, equivalencia de zeros,
certificado Green concreto ou RH.

## Checkpoint da holomorfia e unicidade da continuacao Cp

- commit certificado: `da0585ced6f3922da6b32d57b54f169910357ca7`;
- workflow run: `29665212572` (`Lean kernel audit`);
- job: `88134403089` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`;
- novo alvo compilado: `CPFormal.Analytic.CpBracketHolomorphic`.

Para cada `z` em `Re(s)>-1`, o kernel verificou que a bola de raio
`(Re(z)+1)/2` admite um majorante somavel comum para todos os blocos
bracketados. A constante controla `||s(s+1)||` em toda a bola, e o expoente
usa o piso real `(Re(z)-1)/2>-1`. O criterio de Weierstrass da Mathlib produz
a holomorfia da cauda e da carta completa nesse semiplano.

O kernel tambem verificou que o semiplano e convexo e preconexo e aplicou o
principio da identidade: qualquer funcao analitica em `Re(s)>-1` que coincide
com `(1-p^(1-s))*genuineDirichlet(s)` em `Re(s)>1` coincide com a carta
bracketada em todo o dominio.

Este checkpoint nao identifica `genuineDirichlet` com `riemannZeta`, nao
prova a nao anulacao do fator, equivalencia de zeros, certificado Green
concreto, operador Hilbert--Polya ou RH. Tambem nao exporta um teorema separado
quantificado sobre compactos; o majorante local em bolas e o endpoint usado
para certificar a holomorfia.

## Checkpoint do fator regular e quociente Genuine Cp

- commit certificado: `26379be9ed40c9196bd85af8bcba6b2808cf2481`;
- workflow run: `29667470934` (`Lean kernel audit`, run number 118);
- job: `88140361964` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`;
- novo alvo compilado: `CPFormal.Analytic.CpGenuineQuotient`.

O kernel verificou a identidade de modulo

```text
||p^(1-s)|| = p^(1-Re(s))
```

para primo `p`. A monotonicidade estrita de `Real.rpow` mostra que esse modulo
e maior que um abaixo de `Re(s)=1` e menor que um acima. Consequentemente,
`1-p^(1-s)=0` implica `Re(s)=1`, e o fator nao zera no interior da faixa
critica.

Foi definido `cpGenuineQuotient` como carta dividida pelo fator. O kernel
verificou que ele e holomorfo em `0<Re(s)<1`, coincide com a serie
`genuineDirichlet` em `Re(s)>1` para primo impar e tem zeros equivalentes aos
da carta dentro da faixa.

O indice primo permanece parte da definicao. Este checkpoint nao prova que os
quocientes de primos diferentes coincidem na faixa, nao identifica o objeto
com `riemannZeta`, nao trata multiplicidades, nao constroi certificado Green
concreto, operador Hilbert--Polya ou RH.

## Checkpoint da compatibilidade Genuine entre cameras Cp

- commit certificado: `a31645bbf79a2743ab14bfbd0343c30b8b6f510c`;
- workflow run: `29668593622` (`Lean kernel audit`, run number 123);
- job: `88143422851` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`;
- novo alvo compilado: `CPFormal.Analytic.CpGenuineCompatibility`.

Para primos impares `p,q`, o kernel verificou em `Re(s)>1` a identidade
cruzada entre `F_q*B_p` e `F_p*B_q`. Como ambos os produtos sao holomorfos no
semiplano preconexo `Re(s)>-1`, o principio da identidade prolonga a igualdade
antes de qualquer divisao. Dentro da faixa critica, os fatores sao nao nulos;
o cancelamento prova que os quocientes de `p` e `q` coincidem.

O representante `genuineContinuation`, escolhido pela camera `p=3`, e
portanto independente da camera na faixa, e holomorfo nela e recupera a serie
Genuine no semiplano inicial. Os zeros de qualquer carta prima impar
equivalem aos zeros desse mesmo representante na faixa.

Este checkpoint nao identifica o representante com `riemannZeta`, nao trata
multiplicidades, nao constroi certificado Green concreto, operador
Hilbert--Polya ou RH.

## Checkpoint Green Cp finito e endpoint refletido

- commit certificado: `7b1275cf6af93a3c03be53e80f780127b42c7b6c`;
- workflow run: `29670152564` (`Lean kernel audit`, run number 129);
- job: `88147549171` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`;
- novos alvos compilados: `CPFormal.Analytic.CpFiniteGreen` e
  `CPFormal.Analytic.CpReflectedEndpoint`.

O kernel verificou a telescopagem Green finita com endpoints literais, a
relacao de autovetor `B_p g_s=p^(-s)g_s`, a fatoracao exata do Wronskiano
finito pela diferenca dos autovalores refletidos e a ligacao dos cortes da
carta ao Genuine canonico em `Re(s)>1`.

Tambem verificou, para `s#=1-conj(s)`, que o produto refletido no endpoint
externo e exatamente `(M+1)^(-1)` e tende a zero. O endpoint inicial nao foi
apagado: permanecem abertas sua identificacao com o traco bracketado, a
normalizacao radial, a positividade refletida e a instancia concreta de
`SignedGreenCertificate`. Este checkpoint nao constroi operador
Hilbert--Polya e nao prova RH.

## Checkpoint do certificado Green Cp complexo finito

- commit certificado: `b0b47a87a64acfd129fbeb4f0cac148ccc4114ae`;
- workflow run: `29671533493` (`Lean kernel audit`, run number 131);
- job: `88151337679` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`;
- novo alvo compilado: `CPFormal.Analytic.CpFiniteGreenCertificate`.

O kernel verificou uma estrutura finita que conserva separadamente o
Wronskiano de bloco e a corrente de Stokes. A instancia Cp concreta deriva
`flux=coefficient*energy+boundary`, onde o fluxo e Wronskiano mais Stokes, a
energia e o pareamento refletido e o bordo e a diferenca literal dos
endpoints. O mesmo certificado prova `boundary=1/(M+1)-1`.

O certificado e complexo, nao o `SignedGreenCertificate` real consumido pela
reducao final. A retirada da fase, a positividade da parte real e o
cancelamento do endpoint interno pela porta bracketada permanecem abertos.
Este checkpoint nao constroi operador Hilbert--Polya e nao prova RH.
