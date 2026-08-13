# Auditoria corrigida: zero, tilt e centro Green

## Correção executiva

A versão anterior desta auditoria partia de uma definição semanticamente
incorreta:

```text
native zero := mass compatibility and boundary closure.
```

Essa definição transformava equilíbrio quadrático em parte do significado de
zero. Ela foi removida. A API ativa usa:

```text
native zero := boundary closure.
```

Consequentemente, a antiga “promoção de zero Genuine bruto a zero nativo” não
é um gate matemático: no strip, os dois predicados de anulação já são
equivalentes.

## Três fatos separados

### 1. Equilíbrio quadrático

Antes de funções, primos, operadores ou zeros, a massa posicional e sua
amplitude quadrática fixam:

```lean
NativeCarryRealPlaneMassCompatible sigma time
  ↔ sigma = (1 : ℝ) / 2
```

O tilt e os defeitos radiais fornecem detectores equivalentes desse mesmo
equilíbrio. Eles não são predicados de zero da câmera.

### 2. Identidade de anulação

Para todo `s` em `genuineCriticalStrip`:

```lean
IsNativeCarryRealOperatorZero 3 s.re s.im
  ↔ genuineContinuation s = 0
```

A equivalência usa a identidade finita entre a embalagem da câmera real e a
carta de Dirichlet, seguida da unicidade do limite. Não contém uma hipótese de
massa e não restringe `s.re`.

### 3. Diagnóstico Green

O centro Green detecta o deslocamento
`criticalDisplacement s.re = s.re - 1/2`. Para blocos primos `p,q` e `s` no
strip:

```lean
complexifiedAlignedGreenLimitOperator p q s = 0
  ↔ criticalDisplacement s.re = 0
```

O operador em soma direta preserva os dois testes:

```lean
genuineGreenCompletedLimitOperator p q s = 0
  ↔ IsNativeCarryRealOperatorZero 3 s.re s.im ∧
      s.re = (1 : ℝ) / 2
```

Logo, se houver um zero fora do equilíbrio, a leitura correta é:

```text
camera nativa = 0
Genuine        = 0
centro Green   != 0
operador Genuine direct-sum Green != 0.
```

O canal Green denuncia o defeito transversal; ele não declara que o primeiro
canal “não era zero”.

## Mapa corrigido das interfaces

| Interface | O que ela afirma | O que ela não afirma |
|---|---|---|
| massa--amplitude | o único equilíbrio quadrático é `sigma = 1/2` | inexistência de zeros fora desse equilíbrio |
| câmera real--Genuine | os dois objetos têm o mesmo predicado de anulação no strip | anulação do centro Green |
| embalagem real--complexa | escrever o par real em `ℂ` preserva o zero | confinamento radial |
| Green center | o defeito transversal zera somente em `1/2` | que Genuine só possa zerar ali |
| operador completado | os canais Genuine e Green zeram simultaneamente somente em zero mais equilíbrio | que a não anulação do canal Green revogue um zero Genuine |

## Alterações formais

- `CpNativeCarryRealOperatorZero.lean` substitui o antigo módulo de
  confinamento como fonte canônica.
- `CpNativeCarryRealOperatorConfinement.lean` é apenas um import de
  compatibilidade.
- Foram removidos os teoremas `nativeCarryRealOperatorZero_sigma_eq_half` e
  `nativeCarryRealOperatorZero_ne_of_sigma_ne_half`.
- O zero complexo deixou de carregar compatibilidade de massa.
- O crosswalk Genuine--Green passou a declarar separadamente identidade de
  zeros e anulação do operador completado.
- Os módulos `CpGenuineZeroConfinementAttempt.lean` e
  `CpGenuineOffCriticalCostContradictionProbe.lean` foram removidos por
  dependerem da semântica substituída.
- O certificado universal mantém massa e zero em campos separados.

## Alcance da auditoria

Esta auditoria corrige definições, teoremas derivados e linguagem pública. Ela
não usa a correção para postular a existência de zeros off-equilibrium nem
para provar que todos os zeros estejam no equilíbrio. A afirmação positiva
relevante é arquitetural e kernel-checked:

```text
equilíbrio quadrático vem do carry;
zero vem da anulação;
o centro Green mede o desvio entre os dois.
```

Consulte também `docs/NATIVE_ZERO_SEMANTICS_CORRECTION.md`.
