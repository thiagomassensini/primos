# Normalização cofinal do one-jet C2 em `G_pre`

## Resultado

O módulo

```text
CPFormal/Analytic/CpC2DirichletJetGpre.lean
```

transporta o one-jet de Dirichlet conectado C2 para as pernas de proveniência
da análise TFVD--`G_pre`, normaliza o readout pela própria massa conectada do
pushforward e separa rigorosamente o resultado local do intertwiner global
cofinal ainda necessário.

O checkpoint foi elaborado pelo Lean 4 no commit
`d65d179c3c42be8de7e4e913d6a8289724fb6868`, GitHub Actions run `#441`.

## 1. Readout diretamente da proveniência

Para um contexto de bordo nativo `c`, o coeficiente do papel de valor é

```text
c2GpreProvenanceValueCoefficient c
  = nativeGpreTowerCoordinateCoefficient (c.withRole .value).
```

Uma coordenada ativa da análise enriquecida contém

```text
edgeValue * c2GpreProvenanceValueCoefficient c.
```

O readout

```text
c2GpreNormalizedProvenanceValueReadout
```

divide por esse coeficiente no locus ativo. Ele consulta somente
`data.2.1`, isto é, a perna de valor da proveniência `G_pre`; a reconstrução
TFVD não participa da prova.

Os teoremas

```text
c2GpreNormalizedProvenanceValueReadout_pair_left
c2GpreNormalizedProvenanceValueReadout_pair_right
c2GpreNormalizedProvenancePairReadout_analysis
```

provam que duas tags ativas recuperam exatamente os dois vértices do estado
finitamente suportado.

## 2. Atlas espectral de quatro vértices

A estrutura

```text
C2GpreActiveSpectralAtlas S p q
```

preserva quatro contextos ativos, com células literalmente iguais a

```text
p, p*q, 1, q.
```

Os demais eixos do contexto nativo continuam presentes: primo e tempo
aritméticos, canto, orientação, perna, divisor Jordan, primo e nível da torre.
Nenhum desses rótulos é substituído pelo parâmetro espectral `s`.

As quatro pernas ordinárias e logarítmicas são analisadas separadamente:

```text
c2OddCoreDirichletGpreLowerAnalysis
c2OddCoreDirichletGpreUpperAnalysis
c2OddCoreLogDirichletGpreLowerAnalysis
c2OddCoreLogDirichletGpreUpperAnalysis.
```

Somente depois de recuperar os quatro pares pela proveniência, o readout

```text
c2OddCoreDirichletLogGpreReadout
```

forma as duas células da regra de Leibniz.

O kernel prova

```text
c2OddCoreDirichletLogGpreReadout_eq_spectralGap
```

e portanto

```text
GpreReadout_T(p,q,s)
  = JointPath_T(p,q,s) - FactorizedPath_T(p,q,s)
  = K_T(p,q) * log(p*q) * (p*q)^(-s).
```

Assim, o gap local deixa de ser recuperado pela pseudoinversa TFVD: ele é lido
nas próprias coordenadas tipadas de `G_pre`.

## 3. Normalização pela massa cofinal

A escala conectada do par `4M/8M` é nomeada por

```text
c2OddCoreCofinalMassScale M p q
  = (1/2) * epsilon_M(p) * epsilon_M(q).
```

Depois do transporte pela proveniência, Richardson continua exato:

```text
2 * GpreReadout_(8M)(p,q,s) - GpreReadout_(4M)(p,q,s)
  = c2OddCoreCofinalMassScale(M,p,q)
      * natLogDirichletTerm(s,p*q).
```

Este é o teorema

```text
c2OddCoreDirichletLogGpreReadout_richardson_exact.
```

O quociente cofinal é

```text
c2OddCoreNormalizedCofinalGpreReadout
  = (2 * GpreReadout_(8M) - GpreReadout_(4M))
      / c2OddCoreCofinalMassScale(M,p,q).
```

No locus em que a massa de suporte não é zero, o kernel prova a identidade
finita

```text
c2OddCoreNormalizedCofinalGpreReadout_eq_natLogDirichletTerm
```

isto é,

```text
NormalizedLocalReadout_M(p,q,s)
  = log(p*q) * (p*q)^(-s).
```

O fator geométrico que decai por `1/4` foi removido exatamente.

## 4. Guardrail: a célula local não fecha num zero Genuine

A normalização correta impede a inferência degenerada

```text
C2_M * spectralCell -> 0
```

que seria verdadeira para todo `s` apenas porque `C2_M` tende a zero.

Mas ela também mostra que um único par semiprimo não pode realizar sozinho o
fechamento global. Sob não degenerescência eventual da massa,

```text
c2OddCoreNormalizedCofinalGpreReadout_tendsto_natLogDirichletTerm
```

prova

```text
NormalizedLocalReadout_M(p,q,s)
  -> log(p*q) * (p*q)^(-s).
```

O limite é um átomo de frequência fixo, não zero. Um zero de
`genuineContinuation s` fecha uma soma oscilatória global; ele não anula cada
monômio de Dirichlet separadamente.

Portanto, dividir pelo suporte resolve o falso fechamento geométrico, mas não
substitui a reorganização cofinal entre muitas frequências.

## 5. Gap global das duas câmeras

O objeto global já certificado é nomeado no novo módulo por

```text
c2CrossPrimeCofinalCameraGap p q L s
```

com fórmula

```text
p^(1-s) * positiveDirichletPrefix(s, crossPrimeAlignedCutoff(q,L))
  - q^(1-s) * positiveDirichletPrefix(s, crossPrimeAlignedCutoff(p,L)).
```

Ele contém uma família crescente de frequências. O teorema existente de
sincronização multibase fornece agora diretamente

```text
c2CrossPrimeCofinalCameraGap_tendsto_zero_of_genuine_zero:

  genuineContinuation(s) = 0
    -> c2CrossPrimeCofinalCameraGap(p,q,L,s) -> 0.
```

Aqui o fechamento depende do zero Genuine e do cancelamento oscilatório das
câmeras, não do coeficiente C2 decrescente.

## 6. Intertwiner global restante

A obrigação exata foi isolada como a relação

```text
C2GpreNormalizedCofinalIntertwinesCameraGap
  normalizedProvenanceGap p q s.
```

Ela afirma que uma síntese cofinal concreta das células normalizadas de
proveniência coincide eventualmente com o gap global das câmeras.

Dada essa relação, o kernel já compõe o resultado:

```text
normalizedC2GpreProvenanceGap_tendsto_zero_of_genuine_zero.
```

Nenhuma instância da relação é declarada. O módulo não define a síntese
cofinal como sendo o lado das câmeras e não identifica por decreto os fatores
semiprimos com os módulos de câmera.

A próxima construção matemática precisa, portanto:

1. escolher uma família cofinal de células/fatores no atlas `G_pre`;
2. especificar seus pesos de síntese antes de usar a hipótese de zero;
3. provar uma identidade finita ou um erro relativo entre essa síntese e
   `c2CrossPrimeCofinalCameraGap`;
4. somente então aplicar o teorema de fechamento Genuine já disponível.

## Escopo lógico

Este checkpoint é inteiramente finito até a última composição de limites. Ele
não usa zeta, equação funcional, tabela de zeros ou uma instância de
`Genuine -> Green`.

Ficaram kernel-checked:

- extração das quatro pernas pela proveniência nativa;
- reconstrução bilinear do gap local pelo one-jet;
- Richardson depois do transporte `G_pre`;
- divisão exata pela massa conectada;
- identificação do limite local normalizado;
- fechamento do gap global das câmeras num zero Genuine;
- composição condicional com a relação cofinal restante.

Permanece aberto somente o conteúdo aritmético da síntese cofinal que liga os
dois últimos objetos.