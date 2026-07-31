# Resumo geral — Herança causal do carry

> O que não muda quando a representação muda?
>
> No passo elementar de carry, mudam as coordenadas posicionais, mas o valor
> representado é conservado. Nas operações seguintes, o símbolo pode
> desaparecer, mas sua ancestralidade operacional permanece certificada.

## Registro desta versão

- Repositório: `thiagomassensini/primos`
- Pull request de origem: `#28`
- Versão: `v0.53.0`
- Commit no `main`: o commit resolvido pela tag anotada `v0.53.0`
- Release:
  [v0.53.0](https://github.com/thiagomassensini/primos/releases/tag/v0.53.0)
- Verificação: auditoria estática e `lake build --wfail`
- `sorry`, `axiom` ou `admit` adicionados neste checkpoint: nenhum

O código matemático foi inicialmente certificado no commit
`6bc5ce00305450de54fafeeebca21ab483a18944`, pelo
[workflow 30601161334](https://github.com/thiagomassensini/primos/actions/runs/30601161334),
job `91063922928`.

O primeiro pacote de documentação técnica da branch chegou ao commit
`c66f56edaf328f852cdd3fdc15dbb5c620adea88`, também com CI verde no
[workflow 30601498672](https://github.com/thiagomassensini/primos/actions/runs/30601498672).

Esses dois runs registram a certificação de origem. Para a versão publicada, o
workflow de release é a fonte autoritativa da validação final: a publicação da
release `v0.53.0` somente ocorre depois do sucesso das verificações exigidas
nesse workflow.

## A percepção traduzida para matemática

A estrutura estudada é:

```text
carry posicional
    -> soma posicional
    -> multiplicação
    -> potência natural
```

A afirmação formal não depende apenas de colocar esses nomes em sequência.
Cada seta guarda um certificado matemático concreto:

1. o carry muda a escala posicional preservando exatamente o valor;
2. a soma é reconstruída por dígito restante mais base vezes carry;
3. a multiplicação satisfaz as equações de iteração da soma;
4. a potência natural satisfaz as equações de iteração da multiplicação.

Portanto, existem duas formas diferentes de presença:

- presença explícita: o carry aparece diretamente na descrição da operação;
- presença causal: existe uma cadeia certificada desde o carry primitivo até
  o portador atual, e esse portador possui ação observável não constante.

Multiplicação e potência natural não exibem o carry em sua notação
superficial. Mesmo assim, no sistema formal construído, ambas mantêm sua
ancestralidade causal.

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

## 7. A massa já pertence ao evento de carry

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

## 8. Por que aparece o expoente `1/2`

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

## 9. Certificado consolidado

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

## 10. Independências já estabelecidas

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

## 11. Escopo exato do que foi provado

### Estado `KERNEL_CHECKED`

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

## 12. O que “compressão” significa aqui

Neste checkpoint, compressão significa empacotamento operacional e
genealógico:

- a soma guarda o transporte posicional por quociente e resíduo;
- a multiplicação empacota somas repetidas;
- a potência empacota multiplicações repetidas.

Isso não é, por si só, uma afirmação de compressão com perda de informação,
nem uma afirmação de que operações diferentes têm o mesmo valor. O objeto
conservado no passo primitivo é o valor posicional; nas camadas seguintes, o
que é conservado formalmente é a ancestralidade certificada do mecanismo.

## 13. Mapa dos arquivos

| Função | Arquivo |
|---|---|
| Linguagem abstrata de presença causal | [`CPFormal/Logic/CausalCompression.lean`](../CPFormal/Logic/CausalCompression.lean) |
| Instância carry → soma → multiplicação → potência | [`CPFormal/Carry/PositionalCarryCausalInheritance.lean`](../CPFormal/Carry/PositionalCarryCausalInheritance.lean) |
| Decomposição posicional por quociente e resíduo | [`CPFormal/Carry/PositionalDecomposition.lean`](../CPFormal/Carry/PositionalDecomposition.lean) |
| Probabilidade uniforme do evento de carry | [`CPFormal/Carry/UniformCarryProbability.lean`](../CPFormal/Carry/UniformCarryProbability.lean) |
| Massa e amplitude crítica | [`CPFormal/Carry/CpBranchWeight.lean`](../CPFormal/Carry/CpBranchWeight.lean) |
| Rigidez quadrática do expoente `1/2` | [`CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean`](../CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean) |
| Explicação técnica do checkpoint | [`docs/CARRY_CAUSAL_INHERITANCE.md`](CARRY_CAUSAL_INHERITANCE.md) |
| Este resumo geral | [`docs/RESUMO_GERAL_HERANCA_CAUSAL_DO_CARRY.md`](RESUMO_GERAL_HERANCA_CAUSAL_DO_CARRY.md) |
| Notas da versão imutável | [`docs/RELEASE_0.53.0.md`](RELEASE_0.53.0.md) |
| Estado auditável das alegações | [`docs/CLAIM_LEDGER.md`](CLAIM_LEDGER.md) |
| Registro de compilação e auditoria | [`docs/AUDIT.md`](AUDIT.md) |

## Conclusão

O resultado formal não diz apenas que usamos carry para escrever contas na
escola.

Ele mostra uma cadeia precisa:

```text
saturação posicional
    -> transporte entre escalas com conservação de valor
    -> reconstrução exata da soma
    -> iteração certificada na multiplicação
    -> iteração certificada na potência natural
```

Ao longo dessa cadeia, a forma explícita muda. O carry pode deixar de aparecer
na superfície. O que permanece é a ligação certificada com o mecanismo
primitivo.

Na geometria de profundidade, o mesmo evento possui massa `b^(-k)`. Sua
realização como amplitude quadrática exige `b^(-k/2)`, e a compatibilidade
rigidamente seleciona `1/2`.

Essa é a parte já transformada de percepção estrutural em matemática
verificada. `GeneratedBy` deixa preparada a fronteira formal para investigar
até onde essa herança pode ser estendida sem substituir certificados por
declarações.
