# Certificados inversos restritos da geometria de carry

## Estado deste checkpoint

- versão planejada: `v0.54.0`;
- pull request: `PR #TBD`;
- commit auditado: `commit TBD`;
- GitHub Actions: `workflow TBD`;
- job de kernel: `job TBD`.

Enquanto esses campos permanecerem como `TBD`, este documento registra o
escopo pretendido, mas não promove a nova extensão a `KERNEL_CHECKED`.

## Visão geral

A versão `v0.53.0` certificou a ancestralidade causal direta:

```text
carry
  -> soma posicional
  -> multiplicação
  -> potência natural
```

A extensão `v0.54.0` acrescenta uma camada formal diferente:

```text
carry <-> borrow

soma por y <-> subtração de y, sobre Z

dividendo <-> (quociente, resto), com divisor positivo

multiplicação por d <-> divisão por d, nos múltiplos de d

potência de grau e <-> nthRoot e, nos perfect powers

potência de base b <-> Nat.log b, nas potências exatas
```

Essas relações são pareadas e ramificadas. Elas não formam uma torre inversa
global e não percorrem `CompressionPath` ao contrário.

## Duas responsabilidades formais

### `CausalCompressionSystem`

O sistema da `v0.53.0` responde:

```text
este portador possui ancestralidade causal certificada desde carry?
```

Ele registra portadores, testemunho primitivo, arestas semânticas, caminhos
orientados, ação não constante e presença causal.

### `RestrictedInverseCertificate`

A nova estrutura responde:

```text
em qual domínio,
com quais parâmetros fixos
e com quais dados retidos
estas duas funções formam um round-trip?
```

Sua assinatura abstrata recebe:

- um tipo de origem;
- um tipo de destino;
- uma função `forward`;
- uma função `backward`;
- um predicado `SourceDomain`;
- um predicado `TargetDomain`.

E exige quatro campos:

- `forward_maps_domain`;
- `backward_maps_domain`;
- `left_roundTrip`;
- `right_roundTrip`.

Assim, a ida precisa cair no domínio certificado da volta; a volta precisa
retornar ao domínio certificado da ida; e os dois round-trips precisam ser
identidades dentro desses domínios.

`RestrictedInverseCertificate` é separado de `CausalCompressionSystem`.
Nenhum novo `CausalCompressionSystem` ou `CompressionPath` é construído neste
módulo.

## 1. Carry e borrow

O carry normaliza:

```text
b unidades na profundidade k
  ->
1 unidade na profundidade k+1
```

Borrow expande:

```text
1 unidade na profundidade k+1
  ->
b unidades na profundidade k
```

A conservação é a mesma:

```text
b * b^k = 1 * b^(k+1)
```

As relações são:

- `PositionalCarryStep`
- `PositionalBorrowStep`

O certificado:

- `CarryBorrowReverseCertificate`
- `carryBorrowReverseCertificate`

prova:

- borrow é exatamente a relação carry com os extremos trocados;
- carry preserva o valor;
- borrow preserva o valor;
- a configuração realmente muda.

Esse é um pareamento relacional local. Não é uma função global que recupera
qualquer histórico de normalizações.

## 2. Borrow concreto na subtração posicional

Quando o dígito inferior `x` é menor que o dígito subtraído `y`, uma unidade
da coluna superior é expandida em `b` unidades:

```text
borrowedDigit b x y = x + b - y
```

O valor total da subtração é preservado:

```text
(high - 1)*b + borrowedDigit b x y
  =
high*b + x - y
```

Teorema:

- `positionalBorrow_reconstruction`

Sob as hipóteses escolares

```text
0 <= x < b
0 <= y < b
x < y,
```

o novo dígito retorna à janela canônica:

```text
0 <= borrowedDigit b x y < b.
```

Teorema:

- `borrowedDigit_mem_window`

Certificado:

- `BorrowSubtractionCertificate`
- `borrowSubtractionCertificate`

Esse certificado liga diretamente a mudança de escala por borrow à coluna de
subtração, para toda base `b > 1`.

## 3. Soma e subtração com translação fixa

Para um `y : ℤ` fixo:

```text
addTranslation y x = x + y
subTranslation y x = x - y
```

O Lean registra:

```text
(x + y) - y = x
(x - y) + y = x
```

em todo `ℤ`.

Declarações:

- `addTranslation`
- `subTranslation`
- `subTranslation_eq_add_inverse`
- `AddSubTranslationCertificate`
- `addSubTranslationCertificate`

Os dois domínios são `True`, porque translação por `y` e translação por `-y`
são bijeções de `ℤ`.

Isso não significa que uma soma isolada determine seus dois operandos. O
parâmetro `y` permanece fixo no certificado.

## 4. Divisão euclidiana lossless

Para divisor positivo `d`, define-se:

```text
euclideanSplit d n = (n / d, n % d)

euclideanReconstruct d (q,r) = r + d*q
```

O domínio canônico de destino é:

```text
IsCanonicalEuclideanPair d (q,r) := r < d
```

Teoremas:

- `euclideanSplit_reconstruction`
- `euclideanSplit_remainder_lt`
- `euclideanSplit_recovers_canonicalPair`

Certificado:

- `EuclideanSplitCertificate`
- `euclideanSplitCertificate`

Os dois round-trips são:

```text
reconstruct(split(n)) = n

split(reconstruct(q,r)) = (q,r), quando r < d
```

O ledger lossless é `(d,q,r)`. O quociente sozinho não reconstrói o
dividendo.

## 5. Multiplicação e divisão exata

Para divisor fixo `d`:

```text
mulBy d q = d*q
divBy d n = n/d
```

O domínio de destino é explicitamente a imagem:

```text
IsMultipleImage d n := existe q, n = d*q
```

Para `d > 0`:

```text
(d*q) / d = q
```

Teorema:

- `exactDivision_recovers_factor`

Certificado:

- `MulDivOnMultiplesCertificate`
- `mulDivOnMultiplesCertificate`

Divisão por `d` inverte multiplicação por `d` somente nos múltiplos de `d`.
Para um dividendo arbitrário, o certificado correto continua sendo o split
quociente-resto.

## 6. Potência e `Nat.nthRoot` nos perfect powers

Para grau fixo:

```text
powerByDegree degree value = value^degree
nthRootByDegree degree value = Nat.nthRoot degree value
```

O domínio exato de destino é:

```text
IsPerfectPowerImage degree value :=
  existe root, root^degree = value
```

Para `degree != 0`:

```text
nthRoot degree (value^degree) = value
```

Teoremas:

- `nthRoot_exact_on_powers`
- `nthRoot_reconstructs_iff_perfectPower`

Certificado:

- `PowerNthRootOnPerfectPowersCertificate`
- `powerNthRootOnPerfectPowersCertificate`

O round-trip da direita só é exigido em perfect powers. Uma raiz piso de um
natural arbitrário não é promovida a inversa exata.

## 7. Potência de base fixa e `Nat.log`

Para base fixa `b`:

```text
powerByBase b exponent = b^exponent
floorLogByBase b value = Nat.log b value
```

O domínio exato de destino é:

```text
IsExactBasePower b value :=
  existe exponent, b^exponent = value
```

Para `b > 1`:

```text
Nat.log b (b^k) = k
```

Teorema:

- `floorLog_exact_on_basePowers`

Certificado:

- `BasePowerLogOnExactPowersCertificate`
- `basePowerLogOnExactPowersCertificate`

Potência de base `b` e `Nat.log b` são inversas somente na imagem das
potências exatas da base.

## 8. `Nat.log` conta divisões piso

Para um natural positivo arbitrário:

```text
b^(Nat.log b n) <= n
n < b^(Nat.log b n + 1)
```

Teorema:

- `floorLog_power_window`

Quando `b <= n`, uma divisão inteira por `b` reduz a coordenada em uma
unidade:

```text
Nat.log b n = Nat.log b (n / b) + 1
```

Teorema:

- `floorLog_division_step`

Nesse sentido preciso, `Nat.log` conta divisões piso que atravessam janelas de
magnitude. Ele não é o logaritmo analítico real.

## 9. `positionalDepth` conta divisões exatas

A coordenada:

```text
repeatedExactDivisionDepth b n = positionalDepth b n
```

mede a maior quantidade de divisões exatas por `b`.

Para `b > 1` e `n > 0`:

```text
b^k divide n
b^(k+1) não divide n
```

Teoremas:

- `repeatedExactDivisionDepth_spec`
- `repeatedExactDivisionDepth_factorization_existsUnique`

`Nat.log b n` mede magnitude. `positionalDepth b n` mede divisibilidade. Não
há uma igualdade geral entre eles.

Em base `2`, por exemplo:

```text
positionalDepth 2 12 = 2
Nat.log 2 12 = 3
```

Eles coincidem em potências puras `n = b^k`, mas codificam informações
distintas em geral.

## 10. Bundle consolidado

A estrutura:

- `PositionalInverseArithmeticCertificates`

reúne, para uma base `b > 1`:

- `carry_borrow`;
- `borrow_subtraction`;
- `addition_subtraction`;
- `euclidean_split`;
- `multiplication_division`;
- `power_nthRoot`;
- `power_log`;
- `log_power_window`;
- `log_division_step`;
- `exact_division_depth`.

A instância concreta é:

- `positionalInverseArithmeticCertificates`

Os certificados dependentes de divisor e grau continuam recebendo
explicitamente:

- divisor positivo;
- grau não nulo.

O bundle não apaga essas hipóteses e não converte suas inversas restritas em
uma inversa total comum.

## 11. Relação com massa e `1/2`

Esta extensão não cria uma nova lei de massa.

Continuam como resultados da `v0.53.0`:

```text
criticalMass b k = b^(-k)

criticalAmplitude b k ^ 2 = criticalMass b k

branchAmplitude b sigma k ^ 2 = criticalMass b k
  <->
sigma = 1/2
```

Os novos certificados organizam round-trips e descidas de escala. Eles não
alteram a medida uniforme do evento de carry e não fornecem uma segunda
derivação da rigidez quadrática.

## Escopo e limites

O checkpoint não afirma:

- uma torre inversa global;
- reversão de `CompressionPath`;
- um novo `CausalCompressionSystem`;
- causalidade física ou temporal para trás;
- recuperação dos dois operandos a partir de um resultado escalar;
- divisão lossless usando somente o quociente;
- divisão exata com divisor zero;
- raiz exata fora dos perfect powers;
- `Nat.log` exato fora das potências da base;
- igualdade geral entre `Nat.log b n` e `positionalDepth b n`;
- equivalência entre `Nat.log` e logaritmo real;
- que toda matemática já possui esses certificados;
- nova identidade de massa, amplitude ou rigidez.

## Arquivos

- [`CPFormal/Carry/PositionalCarryInverseCausalInheritance.lean`](../CPFormal/Carry/PositionalCarryInverseCausalInheritance.lean)
- [`CPFormal/Carry/PositionalCarryCausalInheritance.lean`](../CPFormal/Carry/PositionalCarryCausalInheritance.lean)
- [`CPFormal/Logic/CausalCompression.lean`](../CPFormal/Logic/CausalCompression.lean)
- [`docs/RESUMO_GERAL_HERANCA_CAUSAL_DO_CARRY.md`](RESUMO_GERAL_HERANCA_CAUSAL_DO_CARRY.md)
- [`docs/RELEASE_0.54.0.md`](RELEASE_0.54.0.md)

## Próximos passos

1. Executar auditoria estática e `lake build --wfail`.
2. Substituir os quatro campos `TBD` pelos identificadores imutáveis.
3. Criar outros certificados apenas com domínios e dados retidos explícitos.
4. Ligar uma profundidade recuperada à massa somente por novo teorema.
5. Manter separadas ancestralidade causal e inversão restrita.
