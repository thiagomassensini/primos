# Correção semântica: zero, equilíbrio quadrático e centro Green

## Resultado

Este documento substitui toda leitura anterior segundo a qual um zero nativo
seria a conjunção entre compatibilidade de massa e fechamento de fronteira.
Essa conjunção alterava o significado de zero e foi removida da API ativa.

Agora o predicado é literal:

```lean
def IsNativeCarryRealOperatorZero
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  NativeCarryRealOperatorBoundaryClosesAt camera sigma time
```

Portanto:

- zero significa anulação/fechamento;
- a definição vale em qualquer coordenada radial;
- compatibilidade quadrática não é uma condição escondida no zero;
- a embalagem complexa não cria nem remove zeros.

## A ordem matemática

A meia-abscissa nasce antes de qualquer pergunta sobre zeros. Para o estado
real do carry, o kernel já verifica:

```lean
NativeCarryRealPlaneMassCompatible sigma time
  ↔ sigma = (1 : ℝ) / 2
```

Esse enunciado diz onde a amplitude quadrática reproduz a massa posicional.
Ele não afirma que uma função ou câmera não possa zerar em outra coordenada.

Depois vem a anulação. Dentro de `genuineCriticalStrip`, a câmera real nativa
`3` e a continuação Genuine fazem exatamente o mesmo teste:

```lean
IsNativeCarryRealOperatorZero 3 s.re s.im
  ↔ genuineContinuation s = 0
```

O teorema vale para todo `s` do strip e não contém `s.re = 1/2`.

Por fim vem o centro Green. O operador completado preserva em canais separados
o valor Genuine e o deslocamento transversal. O kernel prova:

```lean
genuineGreenCompletedLimitOperator p q s = 0
  ↔ IsNativeCarryRealOperatorZero 3 s.re s.im ∧
      s.re = (1 : ℝ) / 2
```

Equivalentemente, o segundo campo pode ser escrito como
`criticalDisplacement s.re = 0`.

## Leitura correta fora do equilíbrio

Se `s` for um zero nativo/Genuine e `s.re ≠ 1/2`, não há contradição na
definição de zero. As afirmações corretas coexistem:

```text
native/Genuine zero                         = verdadeiro
quadratic mass compatibility                = falso
Green center / completed diagnostic channel = não nulo
```

Essa separação é um único teorema Lean:

```lean
nativeZero_offEquilibrium_channelSeparation
```

Ele conclui simultaneamente que o bloco Genuine é o operador zero e que o
centro Green é não nulo.

O Green aponta o desvio; ele não revoga a anulação do primeiro canal.

## Mudanças na API

- `CpNativeCarryRealOperatorZero.lean` passa a ser a fonte canônica do
  predicado de zero.
- `CpNativeCarryRealOperatorConfinement.lean` permanece somente como import de
  compatibilidade e não exporta teorema de confinamento de zeros.
- `IsNativeCarryComplexOperatorZero` passa a significar somente fechamento
  complexo e é equivalente ao zero real para todo `sigma`.
- `CpNativeGenuineGreenCompletedCrosswalk.lean` separa a identidade de zeros
  da anulação do operador completado.
- Os módulos que tratavam “promoção de zero Genuine a zero nativo” como um
  gate foram removidos: essa promoção agora é a identidade já provada entre
  os dois predicados de anulação.

## Alcance lógico

Esta correção não afirma a existência de um zero fora da meia-abscissa e não
afirma, por definição, que todos os zeros estão nela. Ela certifica a divisão
correta de responsabilidades:

```text
carry/massa  -> seleciona o equilíbrio quadrático
Genuine/nativo -> registra a anulação
Green        -> registra o defeito transversal
```

Os enunciados autoritativos são os tipos Lean compilados; documentos de
releases anteriores que reproduzem a definição substituída devem ser lidos
somente como registro histórico, à luz desta correção.
