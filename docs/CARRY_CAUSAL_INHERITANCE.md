# Heranca causal do carry

Este checkpoint formaliza a observacao estrutural

```text
carry posicional -> soma -> multiplicacao -> potencia natural
```

sem depender de camera prima, base impar ou primalidade.

O ponto central nao e que o simbolo de carry continue escrito em todas as
camadas. O ponto e que cada passagem possui um certificado matematico concreto:

1. a soma e reconstruida exatamente pelo digito restante e pelo quociente de
   carry;
2. a multiplicacao e certificada pelas equacoes de iteracao da soma;
3. a potencia natural e certificada pelas equacoes de iteracao da
   multiplicacao.

Assim, a ausencia do simbolo na notacao final e separada da ausencia causal.

## Traducao da ideia para Lean

O modulo `CPFormal.Logic.CausalCompression` define uma linguagem neutra:

- `PrimitiveWitness`: testemunho de que um portador inicial instancia um
  padrao;
- `CompressionWitness`: certificado de uma passagem entre portadores;
- `CompressionPath`: cadeia transitiva que guarda a existencia desses
  certificados;
- `Reinstantiates`: o padrao chega ao portador por uma cadeia certificada;
- `OperationallyNontrivial`: o portador possui uma acao observavel nao
  constante;
- `CausallyPresentIn`: reinstanciacao certificada junto de acao nao trivial;
- `HiddenButCausallyPresentIn`: o padrao nao aparece na superficie, mas
  permanece causalmente presente;
- `GeneratedBy`: interface para afirmar que todos os portadores de um sistema
  especificado descendem do mesmo padrao.

Essa separacao traduz diretamente a distincao dos documentos de ontologia:
ausencia na representacao final nao implica ausencia na cadeia causal.

O modulo `CPFormal.Carry.PositionalCarryCausalInheritance` fornece a instancia
aritmetica. As unicas arestas permitidas sao:

```text
carryNormalization -> positionalAddition
positionalAddition -> multiplication
multiplication -> naturalPower
```

Todas as outras familias de testemunhos reduzem a `Empty`.

## O que cada certificado prova

### Carry conserva o valor ao mudar de escala

Para qualquer base `b` e profundidade `k`,

```text
b * b^k = 1 * b^(k+1).
```

Em Lean, isso aparece como
`positionalUnitCarry_preserves_value`. As configuracoes antes e depois sao
distintas por `positionalUnitCarry_changes_configuration`.

Portanto, o carry nao acrescenta valor externo. Ele muda as coordenadas da
mesma quantidade entre duas escalas posicionais.

### A soma contem o carry operacional

Para `b > 0` e quaisquer naturais `x,y`,

```text
x + y
  = residueAtDepth b 1 (x+y)
  + b * quotientAtDepth b 1 (x+y).
```

O quociente e positivo exatamente quando a soma da coluna satura a base:

```text
0 < quotientAtDepth b 1 (x+y) <-> b <= x+y.
```

Essas duas propriedades formam o certificado `PositionalCarryCompression`.

### Multiplicacao comprime a iteracao da soma

O certificado `additionToMultiplicationCertificate` guarda:

```text
a * 0 = 0
a * (n+1) = a*n + a.
```

### Potencia natural comprime a iteracao da multiplicacao

O certificado `multiplicationToPowerCertificate` guarda:

```text
a^0 = 1
a^(n+1) = a^n * a.
```

As duas passagens seguintes nao afirmam igualdade numerica entre operacoes
diferentes. Elas registram sua genealogia operacional por equacoes recursivas.

## Teorema causal principal

Para toda base `b > 1`,

```lean
positionalCarry_causallyPresent_through_arithmeticTower
```

prova que o carry esta causalmente presente em cada portador da torre:
normalizacao, soma posicional, multiplicacao e potencia natural.

Os teoremas

```lean
positionalCarry_hiddenButCausallyPresent_in_multiplication
positionalCarry_hiddenButCausallyPresent_in_naturalPower
```

provam a formulacao precisa da sobrevivencia simbolica: multiplicacao e
potencia nao exibem o carry em sua superficie, mas possuem ancestralidade
certificada e acao observavel nao constante.

## Massa ja presente na geometria

O novo modulo nao cria uma massa para o carry. Ele conecta a cadeia causal aos
resultados ja existentes:

```text
uniformCarryEvent_probability = criticalMass b k = b^(-k)
criticalAmplitude b k ^ 2 = criticalMass b k
branchAmplitude b sigma k ^ 2 = criticalMass b k
  <-> sigma = 1/2
```

O teorema consolidado

```lean
positionalCarry_causalInheritance_mass_and_rigidity
```

reune:

- presenca causal escondida na potencia;
- conservacao do valor no carry;
- massa uniforme `b^(-k)`;
- amplitude quadratica;
- rigidez do expoente `1/2`.

Isso formaliza que a massa usada posteriormente ja pertence ao evento de carry
e a sua profundidade; ela nao e inserida por uma camera ou operador posterior.

## Escopo exato

O resultado e universal em relacao a base posicional nao degenerada: exige
somente `b > 1`. Nao exige que `b` seja prima, impar ou igual a `3`.

O predicado generico `GeneratedBy` representa a tese estrutural para qualquer
sistema futuro. Para promover uma nova area da matematica a um teorema dessa
forma, e necessario construir seus portadores, suas avaliacoes nao constantes
e cada certificado de compressao. O codigo atual prova a tese para a torre
aritmetica explicitamente modelada; nao declara sem testemunhos que todos os
objetos matematicos possiveis pertencem a ela.

Essa fronteira e deliberada: a filosofia orienta a estrutura, enquanto cada
afirmacao Lean continua verificavel pelo kernel.
