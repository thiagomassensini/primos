# Checkpoint 0.28.0 — pullback diagonal TFVD do fluxo Green

Este checkpoint fecha a identificacao finita entre a diagonal TFVD do
portador Green e o `finiteOrientedCpGreenFlux` ja formalizado. O alvo
compilado continua sendo `CPFormal.Analytic.CpFinitePortWronskian`.

## Coordenada Green enriquecida

Em cada indice `n`, a nova coordenada

```text
canonicalCpGreenTfvdCoordinate(p,n,s)
```

codifica pela valvula TFVD, com escala de Haar `sqrt(2)` e peso unitario,
as duas arestas

```text
left  = phaseNormalizedCpBlockGradient(p,s,n)
right = positiveDirichletGradient(s,n).
```

O campo `block` e literalmente `n`; portanto a proveniencia sobrevive antes
de qualquer soma.

## Forma refletida no portador TFVD

A forma `tfvdReflectedGreenWedge` e fixa: ela aplica o retorno local ja
provado aos dois portadores TFVD e pareia suas arestas por

```text
conj(right_s) * left_s# - conj(left_s) * right_s#.
```

Ela nao e definida como residual nem a partir do valor do fluxo global. Para
escala e pesos nao nulos, o kernel verificou que `decode(encode(...))`
recupera exatamente essa forma orientada.

## Identificacao coordenada por coordenada

O teorema

```text
tfvdReflectedGreenWedge_canonicalCpGreenCoordinates
```

identifica cada bloco TFVD com o somando orientado do Green. Somando apenas
indices iguais, o kernel verificou

```text
finiteTfvdCpGreenDiagonal(p,M,s)
  = finiteOrientedCpGreenFlux(p,M,s).
```

O teorema final e

```text
finiteTfvdCpGreenDiagonal_eq_finiteOrientedCpGreenFlux.
```

Nao ha termo de erro, calibracao posterior, hipotese de zero, limite ou
cancelamento off-diagonal nessa igualdade.

## Separacao descoberta

Este resultado fecha a diagonal TFVD do portador Green nativo. Ele nao
identifica automaticamente esse portador com as coordenadas angulares
`canonicalAngularTfvdCoordinate` e `canonicalLogJetTfvdCoordinate` que
recuperam `Phi_M` e `Psi_M`.

Logo o gate restante ficou mais preciso:

```text
TFVD angular/log-jet
        ↓ intertwiner tipado ainda aberto
TFVD Green (bloco Cp normalizado, gradiente horizontal)
        ↓ teorema 0.28 fechado
finiteOrientedCpGreenFlux.
```

A interferencia da sintese escalar permanece um segundo gate independente.

## Escopo rigoroso

Este checkpoint ainda nao:

- constroi o intertwiner angular/log-jet para o portador Green;
- prova que o off-diagonal das portas aritmeticas se anula;
- prova uma identidade Wronskiana global ou a passagem ao limite;
- deduz a anulacao do fluxo Green de um zero Genuine;
- identifica o Genuine com `riemannZeta`;
- constroi operador Hilbert--Polya;
- prova a Hipotese de Riemann.

## Evidencia do kernel

- commit matematico: `42bc0ce6d4d64502005a1cef4500a9df36c4f4c5`;
- workflow run: `29714351088` (`Lean kernel audit`);
- job: `88264360190` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`.
