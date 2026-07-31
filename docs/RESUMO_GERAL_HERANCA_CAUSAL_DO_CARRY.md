# Resumo geral — Herança causal direta e inversa do carry

> O que não muda quando a representação muda?
>
> No passo elementar de carry, mudam as coordenadas posicionais, mas o valor
> representado é conservado. Nas operações seguintes, o símbolo pode
> desaparecer, mas sua ancestralidade operacional permanece certificada. No
> sentido pareado, borrow desdobra a escala e as operações inversas recuperam
> estados somente nos domínios e com os dados que seus certificados retêm.

## Registro desta versão

- Repositório: `thiagomassensini/primos`
- Pull request de origem:
  [#29](https://github.com/thiagomassensini/primos/pull/29)
- Versão: `v0.54.0`
- Commit matemático auditado:
  [`8a351323c7476d70e701bed6ab4137d2c5137f2d`](https://github.com/thiagomassensini/primos/commit/8a351323c7476d70e701bed6ab4137d2c5137f2d)
- GitHub Actions:
  [workflow 30607820730](https://github.com/thiagomassensini/primos/actions/runs/30607820730)
- Job de kernel: `91083828864`
- Release:
  [v0.54.0](https://github.com/thiagomassensini/primos/releases/tag/v0.54.0)
- Verificação final exigida: auditoria estática e `lake build --wfail`
- Estado da extensão inversa: `KERNEL_CHECKED`

Nesse head, a auditoria estática e `lake build --wfail` terminaram com
sucesso. A certificação cobre o novo módulo por meio do import ativo em
`CPFormal.lean`. Depois da incorporação, o workflow de release continua sendo
a autoridade sobre o commit exato publicado pela tag.

O checkpoint pai `v0.53.0` permanece certificado. Seu código matemático foi
inicialmente verificado no commit
`6bc5ce00305450de54fafeeebca21ab483a18944`, pelo
[workflow 30601161334](https://github.com/thiagomassensini/primos/actions/runs/30601161334),
job `91063922928`.

O primeiro pacote de documentação técnica da branch chegou ao commit
`c66f56edaf328f852cdd3fdc15dbb5c620adea88`, também com CI verde no
[workflow 30601498672](https://github.com/thiagomassensini/primos/actions/runs/30601498672).

Esses dois runs registram a certificação da família direta em `v0.53.0`. Para
`v0.54.0`, o workflow de release será a fonte autoritativa da validação final:
a tag e a release só podem ser publicadas depois do sucesso das verificações
exigidas nesse workflow.

## A percepção traduzida para matemática

A família direta certificada em `v0.53.0` é:

```text
carry posicional
    -> soma posicional
    -> multiplicação
    -> potência natural
```

A extensão inversa de `v0.54.0` é pareada e ramificada:

```text
carry <-> borrow

soma por y <-> subtração de y, sobre Z

dividendo <-> (quociente, resto)

multiplicação por d <-> divisão por d, nos múltiplos

potência de grau e <-> Nat.nthRoot e, nos perfect powers

potência de base b <-> Nat.log b, nas potências exatas
```

Não existe uma aresta artificial de raiz para logaritmo, nem uma reversão de
`CompressionPath`. A extensão inversa usa certificados restritos separados e
não constrói um novo caminho causal.

Na família direta, cada seta guarda um certificado matemático concreto:

1. o carry muda a escala posicional preservando exatamente o valor;
2. a soma é reconstruída por dígito restante mais base vezes carry;
3. a multiplicação satisfaz as equações de iteração da soma;
4. a potência natural satisfaz as equações de iteração da multiplicação.

Na família inversa:

1. borrow expande uma unidade superior em `b` unidades inferiores sem mudar o
   valor;
2. subtração inverte adição sobre `ℤ` quando o outro operando é retido;
3. divisão euclidiana é lossless somente com quociente e resto;
4. divisão exata recupera o fator somente em múltiplos e com divisor positivo;
5. raiz natural inverte potência somente nos perfect powers certificados;
6. `Nat.log` inverte potência de base fixa somente nas potências exatas;
7. `Nat.log` conta divisões piso, enquanto `positionalDepth` conta divisões
   exatas.

Portanto, existem duas formas diferentes de presença:

- presença explícita: o carry aparece diretamente na descrição da operação;
- presença causal: existe uma cadeia certificada desde o carry primitivo até
  o portador atual, e esse portador possui ação observável não constante.

Multiplicação e potência natural não exibem o carry em sua notação
superficial, mas mantêm a ancestralidade certificada pela família direta. Na
camada inversa, a questão é outra: cada round-trip declara seu domínio e seus
dados retidos, sem inferir presença causal por um novo `CompressionPath`.

## 1. Conservação de valor entre escalas

Uma configuração saturada na profundidade `k` é representada por:

```text
coeficiente = b
profundidade = k
```

Depois da normalização por carry:

```text
coeficiente = 1
profundidade = k + 1
```

As configurações são diferentes, mas representam a mesma quantidade:

```text
b * b^k = 1 * b^(k+1)
```

Isso foi separado em dois teoremas:

- `positionalUnitCarry_preserves_value`
- `positionalUnitCarry_changes_configuration`

Arquivo:

- [`CPFormal/Carry/PositionalCarryCausalInheritance.lean`](../CPFormal/Carry/PositionalCarryCausalInheritance.lean)

Essa é a forma elementar da invariância: o carry não acrescenta uma quantidade
externa. Ele transporta a mesma quantidade para outra escala posicional.

## 2. Carry dentro da soma

Para uma base positiva `b` e naturais `x` e `y`, foram definidos:

```text
digit_b(x,y) = (x+y) mod b
carry_b(x,y) = (x+y) / b
```

O Lean verificou a reconstrução exata:

```text
x + y = digit_b(x,y) + b * carry_b(x,y)
```

Além disso:

```text
carry_b(x,y) > 0  <->  b <= x+y
```

Ou seja, o quociente de carry é positivo exatamente quando a coluna satura a
base.

Teoremas:

- `positionalAddition_reconstruction`
- `positionalAdditionCarry_pos_iff_saturated`

Certificado semântico:

- `PositionalCarryCompression`
- `carryToAdditionCertificate`

A reconstrução usa a decomposição euclidiana geral já provada em:

- [`CPFormal/Carry/PositionalDecomposition.lean`](../CPFormal/Carry/PositionalDecomposition.lean)
- `positionalDecompositionAtDepth`
- `positionalDecompositionAtDepth_existsUnique`

Nada nessa etapa exige base prima ou base ímpar.

## 3. Da soma para a multiplicação

A multiplicação foi registrada como uma operação que empacota a iteração da
soma:

```text
a * 0 = 0
a * (n+1) = a*n + a
```

Estrutura geral:

- `IterationCompression`

Certificado concreto:

- `additionToMultiplicationCertificate`

Essa passagem não afirma que soma e multiplicação possuem o mesmo valor como
operações. Ela registra, por equações recursivas, que a multiplicação é
construída operacionalmente pela iteração da soma.

## 4. Da multiplicação para a potência natural

A potência natural foi registrada como uma operação que empacota a iteração
da multiplicação:

```text
a^0 = 1
a^(n+1) = a^n * a
```

Certificado:

- `multiplicationToPowerCertificate`

Assim, a cadeia completa possui três arestas admitidas:

```text
carryNormalization -> positionalAddition
positionalAddition -> multiplication
multiplication -> naturalPower
```

No tipo `ArithmeticCompressionWitness`, todas as outras combinações de origem
e destino são `Empty`. Isso impede que uma ligação causal seja inserida apenas
por declaração verbal.

## 5. A linguagem geral de presença causal

O arquivo

- [`CPFormal/Logic/CausalCompression.lean`](../CPFormal/Logic/CausalCompression.lean)

define a interface abstrata `CausalCompressionSystem`.

Seus componentes principais são:

- `PrimitiveWitness`: testemunho de que o padrão aparece em um portador
  inicial;
- `CompressionWitness`: certificado matemático de uma passagem direta;
- `CompressionPath`: caminho transitivo composto por passagens certificadas;
- `Reinstantiates`: o padrão alcança um portador por ancestralidade
  certificada;
- `OperationallyNontrivial`: a avaliação do portador não é constante;
- `CausallyPresentIn`: ancestralidade certificada mais ação não trivial;
- `ExplicitlyDisplays`: informa se o padrão aparece na superfície do portador;
- `HiddenButCausallyPresentIn`: presença causal sem exibição explícita;
- `GeneratedBy`: todo portador do sistema possui ancestralidade a partir do
  padrão.

Teoremas gerais importantes:

- `CompressionPath.trans`
- `reinstantiates_of_primitive`
- `reinstantiates_of_compression`
- `reinstantiates_of_path`
- `causallyPresentIn_of_path`
- `causallyPresentIn_all_of_generatedBy`
- `hiddenButCausallyPresentIn_of_witness`

Essa linguagem separa formalmente duas afirmações que não são equivalentes:

```text
o símbolo não aparece
```

e

```text
o padrão não participa da cadeia causal
```

A primeira pode ser verdadeira enquanto a segunda é falsa.

## 6. Teorema principal da torre aritmética

A instância concreta é:

- `positionalArithmeticSystem`

Seus portadores são:

- `carryNormalization`
- `positionalAddition`
- `multiplication`
- `naturalPower`

Os caminhos certificados são:

- `carryToAdditionPath`
- `carryToMultiplicationPath`
- `carryToNaturalPowerPath`

A ancestralidade em cada camada aparece em:

- `carry_reinstantiated_in_addition`
- `carry_reinstantiated_in_multiplication`
- `carry_reinstantiated_in_naturalPower`

Também foi provado que cada portador possui ação observável não constante:

- `carryNormalization_operationallyNontrivial`
- `addition_operationallyNontrivial`
- `multiplication_operationallyNontrivial`
- `naturalPower_operationallyNontrivial`
- `positionalArithmetic_operationallyNontrivial`

A geração da torre pelo carry é certificada por:

- `positionalArithmetic_generatedByCarry`

O teorema causal principal é:

```lean
positionalCarry_causallyPresent_through_arithmeticTower
```

Para toda base `b > 1`, ele prova a presença causal do carry em todos os
portadores explicitamente modelados.

As formas ocultas são certificadas por:

- `positionalCarry_hiddenButCausallyPresent_in_multiplication`
- `positionalCarry_hiddenButCausallyPresent_in_naturalPower`

Esses resultados estão em:

- [`CPFormal/Carry/PositionalCarryCausalInheritance.lean`](../CPFormal/Carry/PositionalCarryCausalInheritance.lean)

## 7. Certificados inversos restritos

A extensão mantém duas linguagens separadas.

`CausalCompressionSystem` responde se um portador possui ancestralidade
causal certificada desde um padrão primitivo e se sua ação observável é não
constante.

`RestrictedInverseCertificate` responde outra pergunta:

```text
sob quais hipóteses,
com quais parâmetros fixos
e com quais dados retidos
uma operação recupera exatamente um estado anterior?
```

Um certificado inverso restrito não reverte um caminho causal e não declara
uma bijeção global. Ele registra o domínio correto do round-trip.

Essa separação impede que:

- uma inversa parcial seja promovida a inversa universal;
- um resultado escalar recupere dados descartados;
- quociente seja confundido com o par quociente-resto;
- raiz piso seja confundida com raiz exata;
- logaritmo piso seja confundido com inversa exata em todo natural.

## 8. Carry e borrow

Carry e borrow leem a mesma conservação em sentidos operacionais pareados:

```text
carry:
b unidades na profundidade k
  ->
1 unidade na profundidade k+1

borrow:
1 unidade na profundidade k+1
  ->
b unidades na profundidade k
```

Em ambos os sentidos:

```text
b * b^k = 1 * b^(k+1)
```

Relações e certificado:

- `PositionalCarryStep`
- `PositionalBorrowStep`
- `CarryBorrowReverseCertificate`
- `carryBorrowReverseCertificate`

O certificado demonstra que borrow troca os extremos da relação carry, que
os dois sentidos preservam valor e que as configurações são distintas.

As coordenadas mudam; o valor não. Borrow não cria uma quantidade externa,
assim como carry não cria.

## 9. Soma e subtração sobre `ℤ`

### Borrow na coluna posicional

Quando `x < y`, define-se:

```text
borrowedDigit b x y = x + b - y
```

e o valor completo da subtração é preservado:

```text
(high - 1)*b + borrowedDigit b x y
  =
high*b + x - y.
```

Sob `0 <= x < b`, `0 <= y < b` e `x < y`, o dígito emprestado volta à
janela `[0,b)`.

Declarações:

- `borrowedDigit`
- `positionalBorrow_reconstruction`
- `borrowedDigit_mem_window`
- `BorrowSubtractionCertificate`
- `borrowSubtractionCertificate`

### Translação por um operando fixo

A inversão é formulada com um operando fixo:

```text
(x + y) - y = x
(x - y) + y = x
```

Também se registra:

```text
x - y = x + (-y)
```

Declarações:

- `addTranslation`
- `subTranslation`
- `subTranslation_eq_add_inverse`
- `AddSubTranslationCertificate`
- `addSubTranslationCertificate`

O uso de `ℤ` evita a truncagem de `Nat.sub`. Isso não significa que uma soma
isolada determine seus dois operandos: o round-trip exige que o deslocamento
`y` permaneça retido.

## 10. Divisão com quociente e resto

Para `d > 0`, define-se:

```text
euclideanSplit d n = (n / d, n % d)
euclideanReconstruct d (q,r) = r + d*q
```

Teoremas:

- `euclideanSplit_reconstruction`
- `euclideanSplit_remainder_lt`
- `euclideanSplit_recovers_canonicalPair`

Certificado:

- `IsCanonicalEuclideanPair`
- `EuclideanSplitCertificate`
- `euclideanSplitCertificate`

O decoder lossless é o ledger `(d,q,r)`, com `r < d`. O split reconstrói todo
dividendo e recupera toda dupla canônica após a reconstrução. O quociente
sozinho não reconstrói o dividendo.

Nos múltiplos exatos:

```text
(d*q) / d = q
```

sob `d > 0`.

Declarações:

- `mulBy`
- `divBy`
- `IsMultipleImage`
- `exactDivision_recovers_factor`
- `MulDivOnMultiplesCertificate`
- `mulDivOnMultiplesCertificate`

Essa é a inversa restrita correta da multiplicação pelo divisor fixo.

## 11. Potência e raiz nos perfect powers

Para grau fixo:

```text
powerByDegree degree value = value^degree
nthRootByDegree degree value = Nat.nthRoot degree value
```

O domínio de destino é explicitamente:

```text
IsPerfectPowerImage degree value
```

Para `degree != 0`:

```text
Nat.nthRoot degree (value^degree) = value
```

Declarações:

- `nthRoot_exact_on_powers`
- `nthRoot_reconstructs_iff_perfectPower`
- `PowerNthRootOnPerfectPowersCertificate`
- `powerNthRootOnPerfectPowersCertificate`

O round-trip da direita só vale nos perfect powers correspondentes. Fora
dessa imagem, `Nat.nthRoot` é uma raiz piso e não é declarada inversa exata
universal.

## 12. Potência e `Nat.log` nas potências exatas

O logaritmo usado aqui é discreto:

```text
floorLogByBase b n = Nat.log b n
```

Para `b > 1`, ele recupera exatamente o expoente na imagem de potência:

```text
Nat.log b (b^k) = k
```

Declarações:

- `powerByBase`
- `floorLogByBase`
- `IsExactBasePower`
- `floorLog_exact_on_basePowers`
- `BasePowerLogOnExactPowersCertificate`
- `basePowerLogOnExactPowersCertificate`

Para um natural positivo arbitrário, ele identifica apenas a janela de
magnitude:

```text
b^(Nat.log b n) <= n
n < b^(Nat.log b n + 1)
```

Teorema:

- `floorLog_power_window`

Quando `b <= n`, uma divisão piso pela base reduz essa coordenada em uma
unidade:

```text
Nat.log b n = Nat.log b (n / b) + 1
```

Teorema:

- `floorLog_division_step`

Assim, `Nat.log` conta semanticamente divisões piso pela base. Ele não é o
logaritmo analítico real.

## 13. Divisão piso e divisão exata não são a mesma profundidade

Foram mantidas duas coordenadas:

```text
floorLogByBase b n
repeatedExactDivisionDepth b n
```

A primeira mede magnitude. A segunda reutiliza `positionalDepth` e mede
divisibilidade exata:

```text
b^k divide n
b^(k+1) não divide n
```

Teoremas:

- `repeatedExactDivisionDepth_spec`
- `repeatedExactDivisionDepth_factorization_existsUnique`

Nenhuma igualdade geral entre `Nat.log b n` e `positionalDepth b n` é
afirmada. Em base `2`, por exemplo:

```text
positionalDepth 2 12 = 2
Nat.log 2 12 = 3
```

Eles coincidem em potências puras `n = b^k`, mas carregam informações
diferentes em geral.

### Bundle de certificados

A estrutura:

- `PositionalInverseArithmeticCertificates`

reúne:

- carry/borrow;
- borrow na subtração posicional;
- translação por soma/subtração;
- split euclidiano;
- multiplicação/divisão nos múltiplos;
- potência/`Nat.nthRoot` nos perfect powers;
- potência/`Nat.log` nas potências exatas;
- janela de magnitude;
- passo de divisão piso;
- profundidade de divisão exata.

A instância:

- `positionalInverseArithmeticCertificates`

preserva as hipóteses de base não degenerada, divisor positivo e grau não
nulo. Nenhum novo `CausalCompressionSystem` ou `CompressionPath` é construído.

## 14. A massa já pertence ao evento de carry

Na profundidade `k`, o espaço de resíduos possui `b^k` classes. Um evento de
carry especificado ocupa uma dessas classes. Sob a medida uniforme finita:

```text
massa = 1 / b^k = b^(-k)
```

Esse cálculo já está certificado por:

- `uniformCarryEvent_probability`

Arquivo:

- [`CPFormal/Carry/UniformCarryProbability.lean`](../CPFormal/Carry/UniformCarryProbability.lean)

A massa é representada por:

- `criticalMass b k = b^(-k)`

A amplitude crítica é:

- `criticalAmplitude b k = b^(-k/2)`

E o Lean verifica:

```text
criticalAmplitude(b,k)^2 = criticalMass(b,k)
```

Teorema:

- `criticalAmplitude_sq_eq_mass`

Arquivo:

- [`CPFormal/Carry/CpBranchWeight.lean`](../CPFormal/Carry/CpBranchWeight.lean)

Portanto, a massa não é introduzida posteriormente por uma câmera ou operador.
Ela já é a medida uniforme do evento posicional na profundidade considerada.

## 15. Por que aparece o expoente `1/2`

Para uma amplitude deformada

```text
branchAmplitude(b,sigma,k) = b^(-k*sigma)
```

o requisito de que sua energia quadrática reproduza a massa do carry é:

```text
branchAmplitude(b,sigma,k)^2 = criticalMass(b,k)
```

Para `b > 1` e `k > 0`, o Lean provou a equivalência:

```text
branchAmplitude(b,sigma,k)^2 = criticalMass(b,k)
    <->
sigma = 1/2
```

Teorema:

- `branchAmplitude_sq_eq_criticalMass_iff_of_one_lt`

Arquivo:

- [`CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean`](../CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean)

O expoente `1/2` não foi escolhido por ajuste numérico neste encadeamento. Ele
é o único expoente real compatível com a realização quadrática da massa
`b^(-k)` em uma profundidade positiva.

## 16. Certificado consolidado

O teorema

```lean
positionalCarry_mass_and_quadraticAmplitude
```

reúne a massa uniforme e a identidade amplitude ao quadrado igual à massa.

O fechamento principal é:

```lean
positionalCarry_causalInheritance_mass_and_rigidity
```

Sob as hipóteses:

```text
b > 1
k > 0
```

ele reúne, numa única conclusão verificada pelo kernel:

1. o carry fica oculto, mas causalmente presente, na potência natural;
2. a normalização por carry conserva o valor representado;
3. o evento uniforme possui massa `b^(-k)`;
4. a amplitude crítica ao quadrado é igual à massa;
5. a amplitude deformada reproduz essa massa se, e somente se,
   `sigma = 1/2`.

Importante: o teorema consolidado conecta resultados certificados que usam os
mesmos parâmetros posicionais. Ele não afirma que a definição abstrata de
presença causal, sozinha, deriva uma medida de probabilidade.

## 17. Independências já estabelecidas

Todo esse checkpoint vale para qualquer base natural não degenerada:

```text
b > 1
```

Ele não exige:

- base prima;
- base ímpar;
- base igual a `3`;
- câmera privilegiada;
- números complexos;
- hipótese externa acrescentada à cadeia;
- postulado novo no Lean.

A base é um sistema de coordenadas posicionais. A conservação e os
certificados não dependem de uma base especial.

## 18. Escopo exato do que foi provado

### Estado `KERNEL_CHECKED` herdado de `v0.53.0`

Está formalmente certificado que:

- o carry muda as coordenadas e conserva o valor;
- a soma possui decomposição exata em dígito e carry;
- a multiplicação empacota a iteração da soma;
- a potência natural empacota a iteração da multiplicação;
- toda a torre aritmética modelada é `GeneratedBy` pelo carry;
- todos os seus portadores são operacionalmente não triviais;
- o carry permanece causalmente presente em toda essa torre;
- multiplicação e potência escondem o padrão na superfície do modelo;
- a massa uniforme do evento é `b^(-k)`;
- a amplitude `b^(-k/2)` realiza essa massa quadraticamente;
- a compatibilidade quadrática força `sigma = 1/2`.

### Estado da extensão `v0.54.0`

A família inversa está em `KERNEL_CHECKED` no commit
`8a351323c7476d70e701bed6ab4137d2c5137f2d`. O workflow `30607820730`, job
`91083828864`, verificou no mesmo head:

- o import no alvo ativo;
- a auditoria estática;
- a ausência local de `axiom`, `sorry` e `admit`;
- a elaboração completa por `lake build --wfail`.

Essa certificação é própria da extensão: ela não foi inferida automaticamente
do sucesso da `v0.53.0`.

### Fronteira ainda aberta

A frase filosófica

```text
todo sistema matemático é gerado pelo carry
```

não foi inserida como axioma nem declarada como teorema universal sem
testemunhos.

Ela foi transformada numa obrigação matemática precisa por meio de
`GeneratedBy`.

Para acrescentar um novo domínio, será necessário:

1. definir seus portadores;
2. definir uma avaliação observável;
3. fornecer o testemunho primitivo;
4. construir um certificado semântico para cada passagem;
5. provar que os portadores relevantes são não constantes;
6. provar a instância correspondente de `GeneratedBy`;
7. aplicar `causallyPresentIn_all_of_generatedBy`.

Essa fronteira não descarta a percepção geral. Ela mostra exatamente o que
precisa ser construído para que cada nova extensão deixe de ser visão e passe
a ser um resultado verificado pelo kernel.

## 19. O que “compressão” e “inversa” significam aqui

Neste checkpoint, compressão significa empacotamento operacional e
genealógico:

- a soma guarda o transporte posicional por quociente e resíduo;
- a multiplicação empacota somas repetidas;
- a potência empacota multiplicações repetidas.

Isso não é, por si só, uma afirmação de compressão com perda de informação,
nem uma afirmação de que operações diferentes têm o mesmo valor. O objeto
conservado no passo primitivo é o valor posicional; nas camadas seguintes, o
que é conservado formalmente é a ancestralidade certificada do mecanismo.

Na extensão inversa, “inversa” significa round-trip restrito:

- com um operando fixo em soma/subtração;
- com divisor positivo e quociente-resto na divisão lossless;
- em múltiplos exatos para recuperar um fator;
- em perfect powers para raiz;
- em potências exatas da base para `Nat.log`.

Não significa inversa funcional universal, recuperação de operandos apagados,
reversão de causalidade ou reversão de `CompressionPath`.

## 20. Mapa dos arquivos

| Função | Arquivo |
|---|---|
| Linguagem abstrata de presença causal | [`CPFormal/Logic/CausalCompression.lean`](../CPFormal/Logic/CausalCompression.lean) |
| Instância carry → soma → multiplicação → potência | [`CPFormal/Carry/PositionalCarryCausalInheritance.lean`](../CPFormal/Carry/PositionalCarryCausalInheritance.lean) |
| Certificados inversos restritos ligados a carry/borrow | [`CPFormal/Carry/PositionalCarryInverseCausalInheritance.lean`](../CPFormal/Carry/PositionalCarryInverseCausalInheritance.lean) |
| Decomposição posicional por quociente e resíduo | [`CPFormal/Carry/PositionalDecomposition.lean`](../CPFormal/Carry/PositionalDecomposition.lean) |
| Probabilidade uniforme do evento de carry | [`CPFormal/Carry/UniformCarryProbability.lean`](../CPFormal/Carry/UniformCarryProbability.lean) |
| Massa e amplitude crítica | [`CPFormal/Carry/CpBranchWeight.lean`](../CPFormal/Carry/CpBranchWeight.lean) |
| Rigidez quadrática do expoente `1/2` | [`CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean`](../CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean) |
| Explicação técnica da família direta | [`docs/CARRY_CAUSAL_INHERITANCE.md`](CARRY_CAUSAL_INHERITANCE.md) |
| Explicação técnica da família inversa | [`docs/CARRY_INVERSE_CAUSAL_INHERITANCE.md`](CARRY_INVERSE_CAUSAL_INHERITANCE.md) |
| Este resumo geral | [`docs/RESUMO_GERAL_HERANCA_CAUSAL_DO_CARRY.md`](RESUMO_GERAL_HERANCA_CAUSAL_DO_CARRY.md) |
| Checkpoint imutável da família direta | [`docs/RELEASE_0.53.0.md`](RELEASE_0.53.0.md) |
| Notas da extensão inversa | [`docs/RELEASE_0.54.0.md`](RELEASE_0.54.0.md) |
| Estado auditável das alegações | [`docs/CLAIM_LEDGER.md`](CLAIM_LEDGER.md) |
| Registro de compilação e auditoria | [`docs/AUDIT.md`](AUDIT.md) |

## Conclusão

O resultado formal direto não diz apenas que usamos carry para escrever
contas na escola. Ele mostra uma cadeia precisa:

```text
saturação posicional
    -> transporte entre escalas com conservação de valor
    -> reconstrução exata da soma
    -> iteração certificada na multiplicação
    -> iteração certificada na potência natural
```

O complemento inverso organiza outra família:

```text
carry <-> borrow com conservação de valor

soma por y <-> subtração de y

dividendo <-> (quociente, resto)

multiplicação <-> divisão nos múltiplos

potência <-> nthRoot nos perfect powers

potência de base b <-> Nat.log nas potências exatas
```

O desenho formal correto é ramificado, e cada round-trip conserva as
hipóteses e os dados necessários.

Na cadeia direta, a forma explícita muda e o carry pode deixar de aparecer na
superfície, embora sua ancestralidade permaneça certificada. Na camada
inversa, o que permanece explícito é o domínio de cada round-trip. Isso não
autoriza recuperar dados que um observador escalar descartou.

Na geometria de profundidade, o mesmo evento possui massa `b^(-k)`. Sua
realização como amplitude quadrática exige `b^(-k/2)`, e a compatibilidade
rigidamente seleciona `1/2`.

A extensão inversa não modifica essa lei anterior. Ela esclarece dois modos de
descer escala: `Nat.log` por divisões piso e `positionalDepth` por divisões
exatas.

A família direta está transformada em matemática verificada desde a
`v0.53.0`, e a família inversa recebeu certificação própria no head
`8a351323c7476d70e701bed6ab4137d2c5137f2d`. `GeneratedBy` e
`RestrictedInverseCertificate` mantêm separadas a ancestralidade causal e a
inversão restrita, permitindo avançar sem substituir certificados por
declarações universais.
