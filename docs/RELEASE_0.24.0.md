# Checkpoint 0.24.0 — caracterizacao exata do fluxo Green acoplado

Este checkpoint reabre o fluxo depois do fechamento do bordo bracketado e
identifica com precisao a ponte que ainda falta. O novo alvo compilado e
`CPFormal.Analytic.CpBracketGreenFlux`.

## Decomposicao independente

O fluxo acoplado havia sido definido subtraindo o mesmo traco bracketado do
fluxo assinado e do bordo. O kernel verificou agora sua forma nao comprimida:

```text
coupledFlux_M
  = Re(orientedBulkFlux_M) + coupledBoundary_M.
```

Usando a fatoracao do Wronskiano radial,

```text
coupledFlux_M
  = radialDifference(p,delta) * Re(reflectedPairing_M)
      + coupledBoundary_M,

delta = Re(s)-1/2.
```

Assim fica visivel que a porta bracketada ja fechada remove o termo de bordo,
mas nao apaga por definicao o bulk radial.

## Lower positivo sem limite de energia

Adicionar uma aresta ao corte adiciona exatamente seu somador ao pareamento.
Como cada aresta tem parte real estritamente positiva na faixa critica, o
kernel provou que

```text
M |-> Re(reflectedPairing_M)
```

e monotono. A partir de `M=1`, todos os cortes ficam acima da parte real da
primeira aresta, que e uma constante estritamente positiva.

Esse lower elimina uma obrigacao que parecia necessaria: nao precisamos saber
primeiro se a energia converge para um limite positivo. Se um multiplicador
constante vezes esses pareamentos converge a zero, o multiplicador precisa ser
zero.

## Caracterizacao nos zeros Genuine

Num zero de `genuineContinuation` na faixa critica, o checkpoint 0.23 ja
garante

```text
coupledBoundary_M -> 0.
```

Com o lower acima, o kernel verificou, para todo primo `p`,

```text
coupledFlux_M -> 0
  <-> radialDifference(p,delta)=0
  <-> delta=0
  <-> Re(s)=1/2.
```

A ida usa a positividade do cofator radial. A volta usa que, em `delta=0`, o
bulk orientado e identicamente zero e sobra apenas o bordo que ja converge a
zero.

## Interpretacao rigorosa

Esse teorema nao prova que os zeros Genuine estao na linha critica. Ele prova
algo estrategicamente importante: **para o fluxo atualmente definido, mostrar
que um zero Genuine anula o fluxo ja e equivalente a obter a linha critica**.

Logo a anulacao nao pode ser tratada como uma consequencia rotineira da mesma
identidade Green radial sem circularidade. Ela precisa vir de uma estrutura
independente, por exemplo uma identidade de fronteira entre

```text
Phi = traco de valor/angular,
Psi = traco de corrente/fluxo.
```

## Escopo rigoroso

Este checkpoint ainda nao:

- constroi os tracos finitos `Phi/Psi`;
- prova uma lei de porta que force o fluxo a zero nos zeros Genuine;
- constroi uma instancia concreta de `SignedGreenCertificate`;
- identifica o Genuine com `riemannZeta`;
- constroi operador Hilbert--Polya;
- prova a Hipotese de Riemann.

## Evidencia do kernel

- commit matematico: `3fcb6d5a05a2395bcdf3d58d94ef6a7a0afd1f38`;
- workflow run: `29706939780` (`Lean kernel audit`);
- job: `88245427884` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`.

## Proximo nucleo minimo

Formalizar primeiro o traco angular finito da camera canonica como soma
ponderada dos gradientes e provar que ele coincide com a carta bracketada ate
um endpoint externo explicito. Depois construir `Psi` e somente entao testar a
identidade Wronskiana de porta que poderia fornecer a direcao ainda aberta.
