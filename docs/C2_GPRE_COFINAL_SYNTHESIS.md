# Síntese cofinal exata dos átomos C2 normalizados em `G_pre`

## Resultado

O módulo

```text
CPFormal/Analytic/CpC2GpreCofinalSynthesis.lean
```

instancia concretamente a relação

```text
C2GpreNormalizedCofinalIntertwinesCameraGap
```

por uma soma finita definida antes de mencionar o gap das câmeras. A síntese
usa átomos log-Dirichlet recuperados diretamente das pernas nativas de
proveniência `G_pre`, aplica pesos explícitos independentes de qualquer hipótese
de zero e reindexa exatamente os dois prefixos alinhados.

O checkpoint foi elaborado pelo Lean 4 no commit
`58d21b0319dbd67d29c320b576339e368ed70d1b`, GitHub Actions run `#446`.

## 1. Por que pares semiprimos, sozinhos, não cobrem a câmera

O átomo conectado já certificado para primos distintos é

```text
NormalizedLocalReadout_M(p,q,s)
  = log(p*q) * (p*q)^(-s).
```

Esse átomo pertence ao suporte squarefree-semiprimo do coeficiente conectado.
Já o prefixo de uma câmera de base `r` contém todas as frequências

```text
r, 2*r, 3*r, ..., cutoff*r,
```

incluindo a semente `r`, potências primas e compostos com qualquer fatoração.
Portanto uma soma restrita a pares de primos distintos não pode ser uma
reindexação finita exata do prefixo completo.

A extensão mínima usada na prova mantém a fórmula atômica

```text
c2GpreNormalizedLogAtom n s = log(n) * n^(-s)
```

em todo índice multiplicativo positivo. No locus `n = p*q`, esse átomo é
literalmente o readout C2 normalizado já construído; fora desse locus ele é a
extensão de suporte necessária para cobrir a câmera inteira.

## 2. Leitura do átomo nas tags nativas

O estado de duas células

```text
c2GpreNormalizedLogAtomAnalysis verticalRatio S n s
```

coloca o átomo na célula `n` e usa a célula zero somente como coordenada dummy.
Para toda tag ativa `c : S` com `c.cell = n`, o teorema

```text
c2GpreNormalizedProvenanceValueReadout_logAtom
```

prova

```text
normalizedProvenanceValueReadout(c, analysis(atom_n))
  = log(n) * n^(-s).
```

A prova consulta apenas a perna de valor da proveniência `data.2.1` e divide
pelo coeficiente nativo da própria tag. Nenhuma reconstrução TFVD participa.

No suporte semiprimo, o teorema

```text
c2GpreNormalizedLogAtom_eq_connectedC2Readout
```

identifica essa extensão com o quociente Richardson/C2 previamente certificado.

## 3. Peso de câmera e cancelamento do gerador logarítmico

Para uma câmera prima `r` e um índice horizontal positivo `m`, defina

```text
cameraAtomWeight(r,m) = r / log(r*m).
```

O átomo ponderado é

```text
weightedCameraAtom(r,m,s)
  = cameraAtomWeight(r,m) * log(r*m) * (r*m)^(-s).
```

Como `r*m > 1`, o logaritmo é não nulo. O kernel prova

```text
c2GpreWeightedCameraAtom_eq_cameraTerm:

weightedCameraAtom(r,m,s)
  = r * (r*m)^(-s).
```

O peso remove somente o gerador logarítmico; não depende de um zero Genuine,
do cutoff ou do deslocamento crítico.

## 4. Reindexação finita de uma câmera

A síntese de uma câmera é definida como soma de átomos:

```text
c2GpreNormalizedCameraPrefixSynthesis r M s
  = sum_{m=1}^M weightedCameraAtom(r,m,s).
```

A multiplicatividade do monômio de Dirichlet e a identidade já existente para
os centros alinhados produzem

```text
c2GpreNormalizedCameraPrefixSynthesis_eq_weightedPrefix:

c2GpreNormalizedCameraPrefixSynthesis r M s
  = r^(1-s) * positiveDirichletPrefix(s,M).
```

A igualdade é finita e não usa série infinita, limite, zeta ou hipótese de
ressonância.

## 5. Síntese cofinal das duas câmeras

Nos cutoffs cruzados, defina

```text
c2GpreNormalizedCofinalSynthesis p q L s
  = cameraSynthesis(p, crossPrimeAlignedCutoff(q,L), s)
      - cameraSynthesis(q, crossPrimeAlignedCutoff(p,L), s).
```

Essa definição contém apenas somas de átomos e seus pesos. Ela não menciona
`c2CrossPrimeCofinalCameraGap`.

A reindexação finita prova, para todo `L`,

```text
c2GpreNormalizedCofinalSynthesis_eq_cameraGap:

c2GpreNormalizedCofinalSynthesis p q L s
  = c2CrossPrimeCofinalCameraGap p q L s.
```

Consequentemente o erro solicitado não é apenas `o(1)`: ele é identicamente
zero,

```text
c2GpreNormalizedCofinalSynthesis_error_tendsto_zero:

||synthesis_L - cameraGap_L|| -> 0.
```

## 6. Instância concreta do intertwiner horizontal

O teorema

```text
c2GpreNormalizedCofinalSynthesis_intertwinesCameraGap
```

fornece uma prova concreta de

```text
C2GpreNormalizedCofinalIntertwinesCameraGap
  (fun L => c2GpreNormalizedCofinalSynthesis p q L s) p q s.
```

Como a igualdade vale em todo cutoff, a condição eventual da relação é
imediata, mas a síntese não foi definida como o lado das câmeras.

Compondo essa instância com o teorema Genuine já existente, o kernel obtém

```text
c2GpreNormalizedCofinalSynthesis_tendsto_zero_of_genuine_zero:

G(s)=0
  -> c2GpreNormalizedCofinalSynthesis(p,q,L,s) -> 0.
```

Esse fechamento é oscilatório e global; o fator geométrico C2 já foi removido
antes da soma.

## 7. Guarda da última seta para o deslocamento crítico

O objeto acima é o gap **horizontal dos prefixos ponderados**. Ele já fecha em
todo zero Genuine, independentemente de uma informação Green adicional.

O pilar que força

```text
criticalDisplacement(s.re) = 0
```

no repositório é o fechamento coordenada a coordenada do fluxo Green,
formalizado por

```text
crossPrimeAlignedGreenClosure_iff_criticalDisplacement_eq_zero.
```

Não é o simples fechamento do prefixo horizontal.

Para impedir que essas duas noções sejam identificadas por nomenclatura, o
novo módulo define

```text
C2GpreHorizontalSynthesisClosureForcesCritical p q
```

e prova

```text
c2GpreHorizontalSynthesisClosureForcesCritical_iff_strongNonvanishing:

C2GpreHorizontalSynthesisClosureForcesCritical p q
  <-> GenuineStrongNonvanishingInStrip.
```

Assim, acrescentar a seta

```text
horizontal synthesis -> delta = 0
```

não seria uma consequência formal menor do intertwiner recém-construído; seria
exatamente o teorema forte de não anulação escalar ainda aberto.

O resultado completado do operador Genuine–Green continua válido e distinto:
o operador em soma direta não zera fora da meia-abscissa porque o bloco Green
retém a informação radial. Isso não implica, isoladamente, que o escalar
`genuineContinuation` não possa zerar fora da linha.

## 8. Estado lógico final

Ficaram kernel-checked:

- recuperação dos átomos log-Dirichlet pelas pernas nativas `G_pre`;
- coincidência com o readout C2 normalizado no suporte semiprimo;
- peso explícito `r/log(r*m)`;
- reindexação finita da síntese para cada câmera;
- igualdade exata da síntese cofinal com o gap horizontal;
- erro de síntese identicamente zero;
- instância concreta de `C2GpreNormalizedCofinalIntertwinesCameraGap`;
- fechamento dessa síntese em todo zero Genuine;
- equivalência entre a seta horizontal adicional para `delta=0` e a não
  anulação forte no strip.

Permanece aberto o transporte adicional que identifique o fechamento dessa
síntese horizontal com o fechamento Green/proveniência radial necessário para
localizar a parte real. Nenhuma instância de inclusão do kernel Genuine no
kernel Green é declarada.

## 9. Validação

- Lean `v4.32.0`;
- `CPFormal`: 8.770 targets com `--wfail`;
- auditoria estática: verde;
- elaboração integral pelo kernel: verde;
- nenhum `sorry`, `admit` ou axioma local;
- GitHub Actions run `#446`: verde.
