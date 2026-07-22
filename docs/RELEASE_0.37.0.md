# Checkpoint 0.37.0 — leque triangular e não-anulamento crítico

Este checkpoint abre geometricamente a parte imaginária que sobreviveu ao
colapso dos traços do 0.36. O novo módulo compilado é
`CPFormal.Analytic.CpFiniteTfvdLogJetCriticalPhaseFan`.

## Leque de fases na linha crítica

Parametrizamos a linha crítica por

```text
s(t) = 1/2 + i t
```

e associamos ao vértice positivo `n+1` o ponto complexo

```text
u_n(t) = positiveDirichletValue(s(t),n).
```

Os pontos `0,u_n(t),u_(n+1)(t)` formam uma face orientada. Sua área é

```text
A_n(t) = 1/2 * Im(conj(u_n(t)) * u_(n+1)(t)).
```

O kernel prova a identidade local exata

```text
crossFlux(n,s(t)) = 4 * A_n(t) * i.
```

Portanto o cross-flux não é apenas uma quantidade abstrata no eixo
imaginário: ele mede literalmente a área orientada da face de fase crítica.
Esta é uma triangulação local em leque, com origem comum `0`; ainda não é o
complexo simplicial aritmético multibase completo.

## Forma senoidal sem aproximação

Definimos

```text
g_n   = log(n+2) - log(n+1),
rho_n = exp(-(log(n+1)+log(n+2))/2).
```

O kernel verifica

```text
g_n > 0,
g_n <= 1/(n+1) <= 1,
rho_n > 0.
```

Abrindo as quatro potências complexas sobre bases reais positivas, com a
escolha de ramo explícita, obtemos

```text
crossFlux(n,s(t))
  = -2 i rho_n sin(t g_n),

A_n(t)
  = -(1/2) rho_n sin(t g_n),

vertexFlux(n,s(t))
  = -2 i g_n rho_n sin(t g_n).
```

Nenhuma expansão assintótica ou identificação com `riemannZeta` é usada.

## Série real de senos

A somabilidade absoluta do 0.34 transporta-se para os coeficientes reais

```text
b_n(t) = -2 g_n rho_n sin(t g_n).
```

Assim o limite residual possui a representação kernel-checked

```text
B(1/2+it) = i * sum_n b_n(t).
```

O perfil também é ímpar:

```text
B(1/2-it) = -B(1/2+it).
```

No centro `t=0`, a série continua nula termo a termo, em acordo com o 0.35.

## Primeira faixa crítica de não-anulamento

Se

```text
0 < t <= 1,
```

então, para todo `n`,

```text
0 < t g_n <= 1 < pi.
```

Logo `sin(t g_n)>0`. Como `g_n` e `rho_n` são estritamente positivos,

```text
b_n(t) < 0
```

para toda face. A soma real absolutamente convergente é, portanto,
estritamente negativa. O kernel conclui

```text
Im(B(1/2+it)) < 0,
B(1/2+it) != 0                 para 0<t<=1.
```

Em particular, há o witness literal

```text
B(1/2+i) != 0.
```

Por imparidade, o sinal se inverte no intervalo refletido `-1<=t<0`.

## Retorno aos traços completos

Combinando o novo não-anulamento com o 0.36, para toda câmera prima `p` e
`0<t<=1` o kernel fecha simultaneamente

```text
ResidualTrace(p,M,s(t))   -> B(s(t)) != 0,
CommutatorTrace(p,M,s(t)) -> 0,
DefectTrace(p,M,s(t))     -> B(s(t)) != 0.
```

O resultado distingue agora os dois canais no limite: o Green radial e o
comutador desaparecem na linha crítica, enquanto o residual triangular
possui uma faixa explícita em que sobrevive.

## Reencontro do carry dentro do Green

O não-anulamento acima mostra que o confinamento não deve exigir
`B(1/2+it)=0`: a parte imaginária triangular pode sobreviver na própria linha
crítica. O detector necessário é transversal.

Para uma base prima, o kernel agora dá nome à identificação exata

```text
cpRadialDifference(p,delta)=0  <->  delta=0
```

e compõe isso com a interface antiga do operador de ramo. No semiplano
`sigma>0`, resulta

```text
branchDefect(p,sigma)=0
  <-> cpRadialDifference(p,sigma-1/2)=0.
```

Portanto a saturação quadrática preparada por `GenuineBranchBridge` e o
fechamento radial desenvolvido pela rota Green são dois detectores do mesmo
locus crítico.

Mais precisamente, se `s` é um zero de `genuineContinuation` no strip, o
kernel prova a equivalência

```text
branchDefect(p,Re(s))=0
  <-> finiteBracketCoupledCpGreenFlux(p,M,s) -> 0.
```

Esta equivalência não prova nenhum de seus lados a partir do zero Genuine.
Ela localiza a única seta que falta e impede circularidade: o fechamento do
fluxo precisa ser derivado independentemente da conclusão `Re(s)=1/2`.

Para registrar essa obrigação sem escondê-la, o módulo introduz
`GenuineCarryFluxBridge`. Seu único campo é exatamente

```text
zero Genuine no strip -> fluxo acoplado fecha.
```

Uma instância concreta dessa estrutura já implica, por composição formal,
`Re(s)=1/2`. Nenhuma instância é postulada neste checkpoint.

## O que a triangulação significa aqui

O objeto formalizado é o leque local

```text
[0,u_n,u_(n+1)]
```

e sua área orientada. Ele não identifica ainda o trio TFVD
`3m,3m+1,3m+2` com o bordo de uma face fechada. Para isso seria necessário
acrescentar e tipar uma aresta de retorno ou transporte direto. Também não
identificamos a área com um defeito de holonomia `Omega`: área/wedge e
curvatura de transporte permanecem objetos distintos até existir um
teorema de comparação.

## Escopo rigoroso

Este checkpoint ainda não:

- liga `B(1/2+it)` a zeros Genuine;
- prova não-anulamento para todo `t != 0`;
- afirma que um zero Genuine anule ou preserve o residual triangular;
- constrói uma instância de `GenuineCarryFluxBridge`;
- deriva o fechamento do fluxo acoplado total de `genuineContinuation s = 0`;
- constrói o complexo simplicial multibase completo ou seu operador de bordo;
- identifica área orientada com defeito triangular de transporte;
- prova somabilidade absoluta dos incrementos já reagrupados do bulk;
- prova cancelamento do off-diagonal aritmético;
- identifica o Genuine com `riemannZeta`;
- constrói operador Hilbert--Polya;
- prova a Hipótese de Riemann.

## Próximo núcleo mínimo

Construir, sem usar previamente `Re(s)=1/2`, uma instância concreta de
`GenuineCarryFluxBridge`. A obrigação analítica mínima é mostrar que, num
zero Genuine, os canais não radiais não produzem uma parte real capaz de
cancelar o bulk

```text
cpRadialDifference(p,delta) * positivePairing(M,s).
```

A triangulação passa a ter uma função cirúrgica: organizar termos
off-diagonal como circulação de faces, cancelar arestas internas por
orientações opostas e reduzir a parte real restante ao bordo externo, que já
fecha nos zeros Genuine. Se essa redução for provada, a composição final já
está pronta:

```text
zero Genuine -> fluxo fecha -> branchDefect=0 -> Re(s)=1/2.
```

O não-anulamento de `B` na linha crítica deixa de ser um obstáculo: ele prova
justamente que não devemos exigir o desaparecimento do residual complexo
inteiro.

## Evidência do kernel

- commit matemático: `bb14de3866035e27e051ca958e042faa73a824cc`;
- workflow run: `29729958305` (`Lean kernel audit`);
- job: `88311846035` (`Build CPFormal`);
- resultado: `success` em auditoria estática e `lake build --wfail`;
- nenhum `sorry`, `admit` ou axioma local.
