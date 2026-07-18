# Checkpoint 0.11.0 — carta finita Cp e criterio Green

Este checkpoint abre a carta Cp em blocos finitos e substitui a ponte final
opaca por um criterio Green com obrigacoes matematicas separadas.

## Abertura finita da carta

O intervalo completo de uma camera recoloca o offset central `0` entre as
`p-1` pernas. O kernel verificou

```text
centerBlock p f center = legSum p f center + f center
```

e, para primo `p`,

```text
bracket p f center
  = centerBlock p f center - p * f center.
```

Somando os centros `p,2p,...,Mp`, isso fornece a identidade exata

```text
finiteChart p M f
  = blockPrefix p M f
    - p * sum_{k<M} f(p(k+1)).
```

Ela vale em qualquer anel comutativo. Nao ha potencia complexa, serie
infinita, zeta ou zero nessa prova.

## Reducao Green verificada

O novo `SignedGreenCertificate` exige quatro fatos independentes:

```text
flux = 2 * criticalDisplacement * radialEnergy + boundary
radialEnergy > 0
genuine(s)=0 -> flux(s)=0
genuine(s)=0 -> boundary(s)=0.
```

O kernel verificou que esses campos forcam

```text
criticalDisplacement(Re(s)) = 0,
Re(s) = 1/2,
cpTiltAtSigma p Re(s) center = 0,
branchNormSq p Re(s) = 1.
```

Em particular, um certificado concreto produz uma
`GenuineBranchBridge` para cada primo.

## Fronteira honesta

Nenhum `SignedGreenCertificate` concreto foi construido. Permanecem abertos:

- o ladrilhamento do `blockPrefix` pelo intervalo positivo literal;
- a especializacao em `n^(-s)` e o controle das caudas;
- o traco de fluxo Genuine;
- a anulacao do termo de bordo no limite.

Portanto este checkpoint nao prova que zeros Genuine saturam o ramo e nao
prova a RH. Ele identifica exatamente quais lemas fechariam essa seta.

## Evidencia de compilacao

- repositorio privado: `thiagomassensini/primos`;
- branch: `agent/lean-kernel-audit`;
- pull request: `#1` (rascunho);
- commit matematico: `e9b8c3d9cd3e13b7085db35b9947743204fcf5b1`;
- workflow run: `29648404437`;
- job verde: `88090470740`;
- resultado: auditoria estatica e `lake build --wfail` concluidos com sucesso.

## Endpoints principais

- `Genuine.Cp.fullOffsets`;
- `Genuine.Cp.centerBlock`;
- `Genuine.Cp.centerBlock_eq_legSum_add_center`;
- `Genuine.Cp.bracket_eq_centerBlock_sub_p_mul_center`;
- `Genuine.Cp.finiteChart_eq_blockPrefix_sub_p_mul_centerSum`;
- `Analytic.Cp.SignedGreenCertificate`;
- `Analytic.Cp.SignedGreenCertificate.criticalDisplacement_eq_zero_of_genuine_zero`;
- `Analytic.Cp.SignedGreenCertificate.toGenuineBranchBridge`;
- `Analytic.Cp.SignedGreenCertificate.cpTiltAtSigma_eq_zero_of_genuine_zero`.
