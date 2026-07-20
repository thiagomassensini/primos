# Checkpoint 0.39.0 — orçamento Green unilateral Genuine-first

Este checkpoint remove uma hipótese excessiva do 0.38. O novo módulo é
`CPFormal.Analytic.CpFiniteGenuineOneSidedGreenBudget`.

## Um único zero é suficiente

O 0.38 fechava o produto angular supondo que `s` e

```text
s# = 1-conj(s)
```

fossem ambos zeros Genuine. O segundo zero não é necessário.

Para `s` no strip, já estava provado que

```text
genuineContinuation(s)=0
  -> Phi_M(s) -> 0.
```

A reflexão preserva o strip. Portanto, independentemente de qualquer zero em
`s#`, a segunda porta possui limite finito:

```text
Phi_M(s#) -> bracketedDirichletChart(3,s#).
```

Pela continuidade do produto,

```text
conj(Phi_M(s)) * Phi_M(s#)
  -> 0 * bracketedDirichletChart(3,s#)
  = 0.
```

Não é usada simetria de zeros, equação funcional, identificação com Zeta ou
qualquer conclusão prévia sobre `Re(s)`.

## Orçamento unilateral

Combinando o limite anterior com a decomposição finita exata do 0.38, o
kernel conclui a partir de um único zero Genuine:

```text
GreenPairing(3M,s) + AngularGreenCorrection(M,s) -> 0.
```

A correção continua separada em

```text
AngularGreenCorrection
  = LocalTrioCorrection + OffDiagonalBlockPairing.
```

Nenhuma das duas parcelas é apagada ou definida como residual tautológico.

## A ponte agora possui um único campo

O módulo introduz `GenuineOneSidedAngularGreenBridge p`. Seu único campo é

```text
genuineContinuation(s)=0
  -> cpRadialDifference(p,delta)
       * AngularGreenCorrection(M,s) -> 0.
```

Não existe campo de zero refletido.

O kernel também prova que a ponte do 0.38 projeta para essa interface
unilateral simplesmente descartando seu campo `reflected_zero`. Isso registra
formalmente que aquele dado não participa mais do argumento.

## Fechamento do tilt sob a única obrigação restante

Multiplicando o orçamento pelo coeficiente radial e subtraindo a correção
escalada, obtemos

```text
cpRadialDifference(p,delta) * GreenPairing(3M,s) -> 0.
```

A parte real do pareamento Green é estritamente positiva no primeiro nível e
monótona nos cutoffs. Ela não pode desaparecer no limite. Logo

```text
cpRadialDifference(p,delta)=0
  -> delta=0.
```

Consequentemente, uma instância futura da ponte unilateral já constrói
`GenuineCarryFluxBridge p` e se compõe com o teorema existente para obter
`Re(s)=1/2` nos zeros Genuine do strip.

## Escopo rigoroso

Este checkpoint ainda não:

- prova o fechamento da correção angular escalada;
- declara uma instância de `GenuineOneSidedAngularGreenBridge`;
- declara uma instância de `GenuineCarryFluxBridge`;
- afirma que `s#` ou `1-s` seja zero quando `s` é zero;
- usa ou prova uma equação funcional;
- identifica o Genuine com `riemannZeta`;
- cancela o off-diagonal por triangulação;
- prova a Hipótese de Riemann.

## Próximo núcleo mínimo

O gargalo agora é único e tipado:

```text
cpRadialDifference(p,delta)
  * (LocalTrioCorrection + OffDiagonalBlockPairing) -> 0.
```

O próximo checkpoint deve separar esse limite em duas obrigações. A correção
local pode ser atacada pelas identidades explícitas dentro de cada trio. A
parcela off-diagonal pode então ser organizada por faces e bordos, sem
misturar novamente proveniências antes do pareamento.

## Evidência do kernel

- commit matemático: `a9a1f1a94944e8af70833726c54da9b30c54ecbd`;
- workflow run: `29735305028` (`Lean kernel audit`);
- job: `88329159656` (`Build CPFormal`);
- resultado: `success` em auditoria estática e `lake build --wfail`;
- nenhum `sorry`, `admit` ou axioma local.
