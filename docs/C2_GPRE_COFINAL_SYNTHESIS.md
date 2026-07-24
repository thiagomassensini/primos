# Síntese cofinal exata dos átomos C2 normalizados em `G_pre`

## Resultado

Os módulos

```text
CPFormal/Analytic/CpC2GpreCofinalSynthesis.lean
CPFormal/Analytic/CpC2GpreCofinalTaggedSynthesis.lean
```

instanciam concretamente a relação

```text
C2GpreNormalizedCofinalIntertwinesCameraGap
```

por uma soma finita definida antes de mencionar o gap das câmeras. A primeira
camada constrói e reindexa os átomos log-Dirichlet. A segunda realiza cada
átomo literalmente como leitura de uma tag ativa na perna nativa de
proveniência `G_pre` e permite que o atlas finito cresça com o nível cofinal.

Os pesos são explícitos e independentes de qualquer hipótese de zero. A
igualdade com o gap horizontal vale em cada cutoff; o erro não é apenas
`o(1)`, mas identicamente zero.

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

Essa extensão está de acordo com a distinção estrutural entre o canal
log-Dirichlet e o canal ordinário: o primeiro fornece o gerador `log(n)`, e a
síntese de câmera aplica depois o peso que remove esse gerador.

## 2. Leitura de um átomo nas tags nativas

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

A síntese escalar de uma câmera é definida como soma de átomos:

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

## 5. Pacote finito de tags de proveniência

Para realizar literalmente a soma no carrier, o tipo

```text
C2GpreActiveCameraPrefixAtlas S r M
```

fornece uma tag nativa para cada índice `k < M`, com

```text
vertex(k).cell = r * (k+1)
nativeCoefficient(vertex(k)) != 0.
```

A síntese tagueada é

```text
c2GpreNormalizedCameraPrefixTaggedSynthesis
  verticalRatio S r M atlas s.
```

Cada termo dessa soma é formado na ordem:

1. inserir o átomo na análise enriquecida;
2. lê-lo em `data.2.1` pela tag correspondente;
3. dividir pelo coeficiente nativo ativo;
4. multiplicar pelo peso `r/log(r*(k+1))`;
5. somar somente depois da leitura coordenada.

O teorema

```text
c2GpreNormalizedCameraPrefixTaggedSynthesis_eq_atomSynthesis
```

prova que a realização tagueada recupera termo a termo a síntese escalar.

## 6. Atlas crescente e síntese cofinal das duas câmeras

O tipo

```text
C2GpreActiveCofinalAtlasFamily p q
```

contém:

```text
support : L -> Finset NativeGpreBoundaryContext
pPrefix : active atlas for p at crossPrimeAlignedCutoff(q,L)
qPrefix : active atlas for q at crossPrimeAlignedCutoff(p,L).
```

Assim, o atlas `support L` pode crescer com o horizonte. A síntese

```text
c2GpreNormalizedCofinalTaggedSynthesis
  verticalRatio family L s
```

é a diferença das duas somas de readouts nativos. Sua definição não menciona o
gap das câmeras.

Primeiro, o kernel prova

```text
c2GpreNormalizedCofinalTaggedSynthesis_eq_atomSynthesis.
```

Depois, pela reindexação finita dos átomos,

```text
c2GpreNormalizedCofinalTaggedSynthesis_eq_cameraGap:

TaggedSynthesis_L(p,q,s)
  = c2CrossPrimeCofinalCameraGap p q L s.
```

A versão escalar paralela é

```text
c2GpreNormalizedCofinalSynthesis_eq_cameraGap.
```

## 7. Erro e instância concreta do intertwiner

Como a igualdade vale em cada cutoff,

```text
c2GpreNormalizedCofinalTaggedSynthesis_error_tendsto_zero:

||TaggedSynthesis_L - CameraGap_L|| -> 0
```

é provado reduzindo a sequência de erros à função constante zero.

O teorema

```text
c2GpreNormalizedCofinalTaggedSynthesis_intertwinesCameraGap
```

fornece a instância concreta

```text
C2GpreNormalizedCofinalIntertwinesCameraGap
  (fun L => TaggedSynthesis_L) p q s.
```

Não há hipótese de igualdade inserida na definição do somador nem hipótese de
zero usada na reindexação.

## 8. Fechamento oscilatório em um zero Genuine

Compondo a instância acima com o teorema Genuine existente, o kernel obtém

```text
c2GpreNormalizedCofinalTaggedSynthesis_tendsto_zero_of_genuine_zero:

G(s)=0 -> TaggedSynthesis_L(p,q,s) -> 0.
```

Esse fechamento é global e oscilatório. O fator geométrico C2 foi removido
antes da soma; a convergência não é produzida pelo decaimento `1/4`.

## 9. Guarda da última seta para o deslocamento crítico

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
módulo escalar define

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

## 10. Estado lógico final

Ficaram kernel-checked:

- recuperação dos átomos log-Dirichlet pelas pernas nativas `G_pre`;
- coincidência com o readout C2 normalizado no suporte semiprimo;
- peso explícito `r/log(r*m)`;
- reindexação finita da síntese para cada câmera;
- pacote de tags ativas em cada prefixo finito;
- família de atlas finitos crescente com o cutoff cofinal;
- igualdade da soma literal de readouts com a síntese atômica;
- igualdade exata da síntese cofinal tagueada com o gap horizontal;
- erro de síntese identicamente zero;
- instância concreta de `C2GpreNormalizedCofinalIntertwinesCameraGap`;
- fechamento dessa síntese em todo zero Genuine;
- equivalência entre a seta horizontal adicional para `delta=0` e a não
  anulação forte no strip.

Permanece aberto o transporte adicional que identifique o fechamento dessa
síntese horizontal com o fechamento Green/proveniência radial necessário para
localizar a parte real. Nenhuma instância de inclusão do kernel Genuine no
kernel Green é declarada.

## 11. Validação

- Lean `v4.32.0`;
- auditoria estática e elaboração integral executadas pelo workflow do PR;
- nenhum `sorry`, `admit` ou axioma local;
- o run e o commit finais são registrados na descrição do PR #8.
