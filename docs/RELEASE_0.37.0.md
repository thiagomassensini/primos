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
- constrói o complexo simplicial multibase completo ou seu operador de bordo;
- identifica área orientada com defeito triangular de transporte;
- cancela o endpoint interno da porta bracket--Green;
- prova somabilidade absoluta dos incrementos já reagrupados do bulk;
- prova cancelamento do off-diagonal aritmético;
- identifica o Genuine com `riemannZeta`;
- constrói operador Hilbert--Polya;
- prova a Hipótese de Riemann.

## Próximo núcleo mínimo

Transportar a separação do limite de volta aos cutoffs finitos: de
`Trace(M) -> B(s(t)) != 0`, extrair um limiar `M_0` após o qual os traços
residual e de defeito permanecem não nulos. Depois disso, uma extensão
natural é ampliar a câmara de sinal usando a cota ótima `g_n<=log 2` e só
então tipar uma verdadeira aresta de retorno para faces TFVD fechadas.

## Evidência do kernel

- commit matemático: `133edecd9d290d948c923bfc92b8ba84eb82c752`;
- workflow run: `29727693258` (`Lean kernel audit`);
- job: `88304489097` (`Build CPFormal`);
- resultado: `success` em auditoria estática e `lake build --wfail`;
- nenhum `sorry`, `admit` ou axioma local.
