# Checkpoint 0.9.0 — pesos de carry, norma de ramo e tilt Cp

Este checkpoint faz a primeira ligacao formal direta entre a profundidade da
bijeção `Cₚ` e a parte quadratica do operador de ramo.

## Peso e amplitude por profundidade

Para uma camada de carry `k`, foram definidos

```text
criticalMass(p,k)      = p^(-k)
criticalAmplitude(p,k) = p^(-k/2).
```

O kernel verificou

```text
criticalAmplitude(p,k)^2 = criticalMass(p,k).
```

Como a igualdade entre profundidade efetiva da perna e `v_p` do centro ja
estava provada, o peso concreto `p^(-k)` atravessa a caixa alinhada pela
bijeção sem termo de bordo.

## Norma quadratica do ramo

Para primo impar `p`, a camera possui `p-1` pernas e profundidade inicial um.
A norma quadratica foi definida pela serie

```text
branchNormSq(p,sigma)
  = (p-1) * sum_{k>=1} p^(-2 k sigma).
```

Para `sigma>0`, o kernel somou a serie e obteve

```text
(p-1) * q / (1-q),   q = p^(-2 sigma).
```

Da cardinalidade geometrica `p-1`, sem constante adicional, segue

```text
branchNormSq(p,sigma) = 1  <->  sigma = 1/2.
```

## Tilt e locus critico

O tilt local usa todas as pernas balanceadas:

```text
Theta_delta^(p)(c)
  = sum_{a in A_p} (c+a)^(-delta) - (p-1)c^(-delta),
delta = sigma - 1/2.
```

O kernel verificou que `delta=0` aniquila o tilt e que defeito nulo da norma
implica tilt nulo em qualquer centro. A volta foi isolada como
`TiltRigidityAt`: ela requer uma prova de sinal/rigidez, ainda nao uma
instancia global.

## A ponte Genuine permanece visivel

`GenuineBranchBridge` e uma estrutura sem instancia cujo campo exigiria

```text
genuine(s)=0 -> branchNormSq(p, Re(s))=1.
```

Condicionalmente a uma instancia dessa estrutura, o kernel ja conclui
`Re(s)=1/2` e tilt nulo. Este checkpoint nao constroi a instancia e, portanto,
nao declara RH provada.

## Evidencia de compilacao

- repositorio privado: `thiagomassensini/primos`;
- branch: `agent/lean-kernel-audit`;
- pull request: `#1` (rascunho);
- commit matematico: `aec9140c36ed5274a8eb7e8a919ef86c0971c5e9`;
- workflow run: `29644692098`;
- job verde: `88080985687`;
- resultado: auditoria estatica e `lake build --wfail` concluidos com sucesso.

## Endpoints principais

- `Carry.Cp.criticalMass`;
- `Carry.Cp.criticalAmplitude`;
- `Carry.Cp.criticalAmplitude_sq_eq_mass`;
- `Carry.Cp.criticalMass_reindex_alignedBox`;
- `Analytic.Cp.branchNormSq`;
- `Analytic.Cp.branchNormSq_eq_closed`;
- `Analytic.Cp.branchNormSq_eq_one_iff`;
- `Analytic.Cp.branchDefect_eq_zero_iff_criticalDisplacement_eq_zero`;
- `Analytic.Cp.cpTilt`;
- `Analytic.Cp.branchDefect_zero_implies_cpTiltAtSigma_zero`;
- `Analytic.Cp.TiltRigidityAt`;
- `Analytic.Cp.GenuineBranchBridge`.
