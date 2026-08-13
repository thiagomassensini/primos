# CPFormal v0.62.0 — correção semântica do zero nativo

## Estado da release

- release pai: `v0.61.0`;
- tag anotada planejada: `v0.62.0`;
- Zenodo concept DOI estável: `10.5281/zenodo.21483474`.

Esta é uma release corretiva. A tag histórica `v0.61.0` permanece imutável;
a `v0.62.0` publica a API ativa já corrigida e fornece a versão canônica para
novos consumidores.

## Resultado

O zero nativo volta a significar exatamente anulação da câmera:

```lean
def IsNativeCarryRealOperatorZero
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  NativeCarryRealOperatorBoundaryClosesAt camera sigma time
```

Compatibilidade de massa não integra essa definição. A arquitetura formal é:

```text
carry/massa       -> equilíbrio quadrático sigma = 1/2
câmera/Genuine    -> anulação
centro Green      -> diagnóstico do deslocamento sigma - 1/2
```

## Identidade de zeros no strip

Para todo `s` no strip Genuine aberto, o Lean prova:

```lean
IsNativeCarryRealOperatorZero 3 s.re s.im
  ↔ genuineContinuation s = 0
```

Não existe hipótese `s.re = 1/2` nesse teorema. A embalagem complexa também
preserva o mesmo predicado de zero para todo `sigma`.

## Separação Green fora do equilíbrio

O operador completado possui dois canais independentes. No mesmo strip:

```lean
genuineGreenCompletedLimitOperator p q s = 0
  ↔ IsNativeCarryRealOperatorZero 3 s.re s.im ∧
      s.re = (1 : ℝ) / 2
```

Portanto, se for apresentado um zero nativo/Genuine com
`s.re ≠ (1 : ℝ) / 2`, o zero não é revogado. O teorema
`nativeZero_offEquilibrium_channelSeparation` conclui:

```text
canal Genuine = 0
canal Green   ≠ 0
```

O Green denuncia o tilt; ele não redefine a anulação.

## Migração da API

Símbolos e leituras anteriores devem ser migrados assim:

| Forma anterior | Forma canônica na v0.62.0 |
|---|---|
| zero como `MassCompatible ∧ BoundaryCloses` | `IsNativeCarryRealOperatorZero`, somente fechamento |
| `NativeCarryRealPlaneAdmissibleFiniteZero` | separar compatibilidade de massa da hipótese de zero |
| `NativeCarryRealPlaneAdmissibleBoundaryClosesAt` | separar compatibilidade de massa de `NativeCarryRealOperatorBoundaryClosesAt` |
| “zero fora de `1/2` não é zero” | zero preservado; canal Green não nulo fora do equilíbrio |
| promoção Genuine → zero nativo | identidade direta dos predicados no strip |

Os módulos-folha que apresentavam confinamento como parte da semântica do
zero foram removidos da API ativa. O script `scripts/static_audit.sh` rejeita
a reintrodução dos símbolos obsoletos e rejeita `MassCompatible` dentro da
definição pública de zero.

## Escopo lógico

Esta release não afirma que exista um zero fora da meia-abscissa e não afirma
que todos os zeros estejam nela. Ela prova e preserva a distinção necessária
para qualquer investigação posterior:

```text
equilíbrio não é definição de zero;
zero não apaga o diagnóstico Green;
diagnóstico Green não revoga um zero.
```

## Verificação e publicação

O workflow da release executa, sobre o commit exato de `main`:

- auditoria estática da API e dos imports;
- testes numéricos de regressão;
- `lake build --wfail` pelo kernel Lean;
- construção e restauração de um bundle Git completo;
- comparação do manifesto de refs e verificação SHA-256 dos artefatos.

Somente depois dessas etapas o workflow cria a tag anotada, publica a GitHub
Release e emite o evento consumido pela integração do Zenodo.

Consulte também
[`NATIVE_ZERO_SEMANTICS_CORRECTION.md`](NATIVE_ZERO_SEMANTICS_CORRECTION.md)
para a justificativa formal detalhada.
