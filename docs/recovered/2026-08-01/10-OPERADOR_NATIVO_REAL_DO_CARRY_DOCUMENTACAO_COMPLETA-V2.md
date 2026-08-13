---
title: "Operador real de carry — documentação canônica completa"
aliases:
  - "Operador nativo"
  - "Operador real de carry"
tags:
  - carry
  - operador-real
  - bracket
  - Lean4
status: "canônico"
checkpoint: "thiagomassensini/primos@7d8d0b345b329935674edc24e5ac08ad9f7b5804"
release: "v0.52.0"
architecture: "thiagomassensini/native-carry-geometry"
date: 2026-07-29
revised: 2026-07-29
---

> **Arquivo histórico.** A definição antiga que incluía compatibilidade de
> massa no “zero nativo” foi substituída. Consulte
> `docs/NATIVE_ZERO_SEMANTICS_CORRECTION.md`.

# Operador real de carry

## Definição completa, geometria, zero, confinamento, representações e auditoria numérica

> [!IMPORTANT]
> A autoridade matemática final é o tipo elaborado pelo kernel do Lean.
> Este documento explica a construção, expande as fórmulas e separa com
> precisão o que está provado, o que é definição, o que é uma identificação de
> representação e o que é evidência numérica finita.

<!-- camera-invariance-guardrail -->

> [!WARNING]
> Não reabrir a invariância de câmera exigindo igualdade definicional entre
> todos os predicados brutos. O fechamento auditado é a composição entre
> independência da base, equivalência dos domínios quadráticos, lei terminal
> universal e representante normalizado comum. A câmera $3$ é escolhida
> somente depois dessa equivalência.

---

## 1. Checkpoint auditado e autoridade documental

| Item | Referência |
|---|---|
| Repositório oficial planejado | [`thiagomassensini/native-carry-geometry`](https://github.com/thiagomassensini/native-carry-geometry) |
| Repositório histórico de proveniência | [`thiagomassensini/primos`](https://github.com/thiagomassensini/primos) |
| Baseline do confinamento | [`89ba6b536686dc05e9186f543b01e72f00b00ad3`](https://github.com/thiagomassensini/primos/commit/89ba6b536686dc05e9186f543b01e72f00b00ad3), tag `v0.51.0` |
| Costuras fundacionais | [PR #18](https://github.com/thiagomassensini/primos/pull/18), commit [`d8d905b3653a03e5a0d3ed09b2c096e351c060b2`](https://github.com/thiagomassensini/primos/commit/d8d905b3653a03e5a0d3ed09b2c096e351c060b2) |
| Crosswalk real–analítico integrado | [PR #19](https://github.com/thiagomassensini/primos/pull/19), checkpoint [`8cee49af8fefc4baef61c1dc27ee5eabcf071878`](https://github.com/thiagomassensini/primos/commit/8cee49af8fefc4baef61c1dc27ee5eabcf071878) |
| Release histórica consolidada | [`v0.52.0`](https://github.com/thiagomassensini/primos/releases/tag/v0.52.0), tag sobre [`7d8d0b345b329935674edc24e5ac08ad9f7b5804`](https://github.com/thiagomassensini/primos/commit/7d8d0b345b329935674edc24e5ac08ad9f7b5804) |
| Arquivamento | [Zenodo `10.5281/zenodo.21681625`](https://doi.org/10.5281/zenodo.21681625) |

Este texto usa os nomes Lean históricos para localizar as provas já verdes em
`primos` e, quando necessário, registra também a nomenclatura acadêmica
planejada para `native-carry-geometry`. Uma obrigação de **portabilidade** para
o repositório novo não deve ser confundida com uma obrigação matemática
aberta: o confinamento, a ponte entre os domínios quadráticos e o crosswalk de
bordo já possuem origem elaborada pelo kernel no repositório histórico.

Para resolver divergências de interpretação, a ordem de autoridade adotada
aqui é:

1. o tipo elaborado pelo kernel do Lean;
2. `MEMORIA_CANONICA_CARRY_AO_OPERADOR(2).md`;
3. `ARQUITETURA_OFICIAL_NATIVE_CARRY_GEOMETRY(1)(1).md`;
4. esta documentação explicativa.

---

## 2. Resultado em uma página

O estado real associado a um inteiro positivo é

$$
u_{\sigma,t}(n)
=
n^{-\sigma}
\bigl(
\cos(-t\log n),
\sin(-t\log n)
\bigr)
\in\mathbb R^2.
$$

Sua energia quadrática é

$$
\|u_{\sigma,t}(n)\|^2
=
n^{-2\sigma},
$$

independentemente de $t$.

O domínio do operador exige que essa energia reproduza a massa inversa:

$$
\|u_{\sigma,t}(n)\|^2=n^{-1}
\qquad
\text{para todo }n>1.
$$

O Lean prova:

$$
\operatorname{MassCompatible}(\sigma,t)
\iff
\sigma=\frac12.
$$

Uma câmera $c$ aplica segundas diferenças centradas ao estado e produz um
resultante finito

$$
R_{c,M}(\sigma,t)\in\mathbb R^2.
$$

O fechamento de bordo é

$$
R_{c,M}(\sigma,t)\longrightarrow(0,0)
\qquad(M\to\infty).
$$

A ressonância nativa é esse fechamento já na casca $\sigma=\frac12$. O zero
do operador real de carry junta as duas partes da construção:

$$
\operatorname{Zero}_{c}(\sigma,t)
:=
\operatorname{MassCompatible}(\sigma,t)
\land
\bigl(R_{c,M}(\sigma,t)\to0\bigr).
$$

O teorema terminal é:

```lean
theorem isNativeCarryRealOperatorZero_iff
    (camera : ℕ) (sigma time : ℝ) :
    IsNativeCarryRealOperatorZero camera sigma time ↔
      sigma = (1 : ℝ) / 2 ∧
        IsNativeCarryRealOperatorResonance camera time
```

Em notação de conjuntos:

$$
\boxed{
Z_c
=
\left\{\frac12\right\}
\times
\mathcal R_c
}
$$

onde

$$
\mathcal R_c
=
\left\{
t\in\mathbb R:
R_{c,M}\left(\frac12,t\right)\to0
\right\}.
$$

Essa escrita câmera a câmera não fragmenta o fenômeno. O fechamento lógico
auditado possui três níveis complementares:

$$
\forall b,d>1,\qquad
\operatorname{PositionalMassCompatible}_b(\sigma)
\iff
\operatorname{PositionalMassCompatible}_d(\sigma)
\iff
\sigma=\frac12;
$$

$$
\operatorname{PositionalMassCompatible}_b(\sigma)
\iff
\operatorname{RealEnergyCompatible}(\sigma,t);
$$

e, no atlas analítico normalizado, as câmeras recuperam o mesmo representante
canônico antes que a câmera $3$ seja escolhida para nomeá-lo.

Portanto, a invariância de câmera da teoria significa que a base ou a largura
escolhida não altera o domínio quadrático, a lei radial nem o fenômeno
canônico observado. Cartas brutas podem ter fórmulas locais distintas; essa
diferença de apresentação não cria operadores físicos ou conjuntos de zeros
concorrentes.

Portanto:

- o carry fixa a coordenada radial;
- a câmera apresenta localmente a ressonância do fenômeno global;
- o tempo gira o estado, mas não altera sua energia;
- o bracket não escolhe novamente o expoente;
- a lei terminal vale simultaneamente para todo `camera : ℕ`, sem hipótese de
  primalidade ou paridade;
- o predicado de zero do operador conserva a compatibilidade de massa como
  parte do domínio.

---

## 3. O que a palavra “operador” significa aqui

No módulo terminal não existe uma única definição Lean do tipo

```lean
def NativeCarryRealOperator : X → Y := ...
```

O nome “operador real nativo” designa uma construção composta por:

1. um campo de estados reais $u_{\sigma,t}(n)$;
2. uma câmera aditiva finita;
3. uma sequência de resultantes $R_{c,M}(\sigma,t)$;
4. um predicado de compatibilidade de massa;
5. um predicado de fechamento no limite;
6. um predicado de ressonância;
7. um predicado de zero.

Essa precisão é importante. O teorema principal classifica exatamente o
predicado `IsNativeCarryRealOperatorZero`; ele não declara a existência de um
novo mapa linear total cujo valor já seria um limite.

Na arquitetura oficial, a mesma construção receberá nomes menores e
acadêmicos:

| Nome histórico | Nome oficial planejado |
|---|---|
| `NativeCarryRealPlane` | `RealCarryPlane` |
| `nativeCarryRealPlaneSampleAt` | `realCarryState` |
| `NativeCarryRealPlaneMassCompatible` | `RealCarryEnergyCompatible` |
| `NativeCarryRealOperatorBoundaryClosesAt` | `BoundaryConvergesToZero` |
| `IsNativeCarryRealOperatorResonance` | `IsBoundaryResonance` |
| `IsNativeCarryRealOperatorZero` | `IsRealCarryOperatorZero` |

O nome acadêmico do resultado terminal é **Real Carry Operator Zero-Set
Factorization Theorem**. A renomeação não altera o objeto matemático nem sua
assinatura lógica.

---

## 4. Notação

| Símbolo | Significado |
|---|---|
| $b$ | base posicional natural, com $b>1$ |
| $k$ | profundidade positiva de carry |
| $c$ | largura ou rótulo natural da câmera |
| $h_c$ | semialcance da câmera, $h_c=\lfloor(c-1)/2\rfloor$ |
| $M$ | cutoff; número de centros incluídos |
| $\sigma$ | expoente radial real |
| $t$ | tempo ou fase logarítmica real |
| $u_{\sigma,t}(n)$ | estado real do inteiro $n$ |
| $\Delta_r^2 f(q)$ | segunda diferença centrada no centro $q$, raio $r$ |
| $R_{c,M}(\sigma,t)$ | resultante vetorial da câmera finita |
| $\mathcal R_c$ | conjunto dos tempos ressonantes da câmera $c$ |
| $Z_c$ | conjunto de zeros do operador real de carry na câmera $c$ |

No Lean,

```lean
def halfRange (c : ℕ) : ℕ :=
  (c - 1) / 2
```

usa divisão natural. Portanto,

$$
h_c=\left\lfloor\frac{c-1}{2}\right\rfloor.
$$

Fonte:
[`halfRange`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Genuine/BalancedOffsets.lean#L16-L17).

---

## 5. Origem posicional: profundidade, massa e amplitude

### 5.1. A profundidade nasce do carry

A fundação auditada começa antes de qualquer câmera prima. Para toda base
natural $b>1$, o PR #18 formaliza:

```lean
positionalDecompositionAtDepth_existsUnique
positionalDepth_factorization_existsUnique
```

Em linguagem matemática, há uma decomposição quociente–resíduo canônica em
cada profundidade e uma fatoração única na profundidade máxima:

$$
n=b^k m,
\qquad
b\nmid m.
$$

Isso define a coordenada vertical sem depender de primalidade. A geometria
binária recebe um módulo próprio, e as câmeras balanceadas ímpares recebem a
decomposição centro–offset correspondente.

Na apresentação histórica das câmeras balanceadas, a profundidade efetiva é o
maior carry entre os offsets, o centro canônico tem sua profundidade própria e
o Lean prova:

$$
\boxed{
\operatorname{effectiveDepth}(b,n)
=
\operatorname{centerDepth}(b,n).
}
$$

Fontes:

- [`PositionalDecomposition.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Carry/PositionalDecomposition.lean), com
  `positionalDecompositionAtDepth_existsUnique` e
  `positionalDepth_factorization_existsUnique`;
- [`effectiveDepth`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Carry/CpDepth.lean#L41-L42);
- [`centerDepth`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Carry/CpDepth.lean#L45-L49);
- [`effectiveDepth_eq_centerDepth`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Carry/CpDepth.lean#L107-L118).

Assim, o índice vertical $k$ é determinado pela aritmética posicional antes da
construção do estado, do bracket ou do operador.

### 5.2. Massa crítica e amplitude crítica

Sob a distribuição uniforme de resíduos módulo $b^k$, o evento de carry que
alcança ao menos a profundidade $k$ é a classe residual zero e tem
probabilidade

$$
\boxed{
\mathbb P(\text{carry até a profundidade }k)=\frac1{b^k}=b^{-k}.
}
$$

Essa origem probabilística já está elaborada em
[`uniformCarryEvent_probability`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Carry/UniformCarryProbability.lean),
verde no PR #18. A massa não é apenas uma notação sugerida pela frequência:
ela é o valor provado do evento uniforme.

Para uma base natural $b$ e uma profundidade $k$, o código define:

$$
\mu_{b,k}=b^{-k},
$$

$$
\alpha_{b,k}=b^{-k/2},
$$

$$
\alpha_{b,k}(\sigma)=b^{-k\sigma}.
$$

Em Lean:

```lean
def criticalMass (b k : ℕ) : ℝ :=
  (b : ℝ) ^ (-((k : ℝ)))

def criticalAmplitude (b k : ℕ) : ℝ :=
  (b : ℝ) ^ (-((k : ℝ)) / 2)

def branchAmplitude (b : ℕ) (sigma : ℝ) (k : ℕ) : ℝ :=
  (b : ℝ) ^ (-((k : ℝ)) * sigma)
```

O quadrado da amplitude crítica é a massa:

$$
\boxed{
\alpha_{b,k}^2=\mu_{b,k}
}
$$

Fontes:

- [`criticalMass`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Carry/CpBranchWeight.lean#L33-L35);
- [`criticalAmplitude`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Carry/CpBranchWeight.lean#L37-L39);
- [`branchAmplitude`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Carry/CpBranchWeight.lean#L41-L43);
- [`criticalAmplitude_sq_eq_mass`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Carry/CpBranchWeight.lean#L59-L66).

### 5.3. Rigidez quadrática

Para $b>1$ e $k>0$:

$$
\alpha_{b,k}(\sigma)^2=\mu_{b,k}
$$

equivale a

$$
b^{-2k\sigma}=b^{-k},
$$

e portanto

$$
\boxed{
\sigma=\frac12.
}
$$

O Lean prova a equivalência completa:

```lean
theorem branchAmplitude_sq_eq_criticalMass_iff_of_one_lt
    (b k : ℕ) (hb : 1 < b) (hk : 0 < k) (sigma : ℝ) :
    (branchAmplitude b sigma k) ^ 2 = criticalMass b k ↔
      sigma = (1 : ℝ) / 2
```

Também prova que a compatibilidade em todas as profundidades tem exatamente o
mesmo singleton de expoentes:

```lean
theorem positionalCarryMassCompatible_iff
    (b : ℕ) (hb : 1 < b) (sigma : ℝ) :
    PositionalCarryMassCompatible b sigma ↔
      sigma = (1 : ℝ) / 2
```

E prova a independência da base no locus de saturação:

$$
\operatorname{BranchNormSq}(b,\sigma)=1
\iff
\operatorname{BranchNormSq}(d,\sigma)=1.
$$

Fontes:

- [`branchAmplitude_sq_eq_criticalMass_iff_of_one_lt`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean#L44-L66);
- [`PositionalCarryMassCompatible`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean#L72-L77);
- [`positionalCarryMassCompatible_iff`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean#L80-L96);
- [`positionalPlaneEnergy_rotatedShell_eq_criticalMass_iff`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean#L162-L177);
- [`branchNormSq_eq_one_iff_of_one_lt`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean#L272-L282);
- [`branchNormSq_eq_one_base_independent`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean#L286-L295).

### 5.4. Crosswalk dos domínios quadráticos

A cadeia por profundidade usa $b^{-k}$; o estado real indexado pelo inteiro usa
$n^{-2\sigma}$ e o compara com $n^{-1}$. A teoria não afirma a igualdade falsa

$$
b^{-k}=n^{-1}
$$

para cada amostra. A costura correta, provada no PR #18, é a equivalência dos
**domínios admissíveis**:

```lean
theorem positionalCarryMassCompatible_iff_realEnergyCompatible
    (b : ℕ) (hb : 1 < b) (sigma time : ℝ) :
    PositionalCarryMassCompatible b sigma ↔
      NativeCarryRealPlaneMassCompatible sigma time
```

Fonte:
[`CpQuadraticDomainCrosswalk.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpQuadraticDomainCrosswalk.lean).

Os dois lados são equivalentes a $\sigma=\frac12$. Portanto:

$$
\boxed{
\forall b>1,\qquad
\operatorname{PositionalMassCompatible}_b(\sigma)
\iff
\operatorname{RealEnergyCompatible}(\sigma,t)
\iff
\sigma=\frac12.
}
$$

Esse teorema fecha a passagem formal:

$$
\text{carry por profundidade}
\longrightarrow
\text{domínio quadrático comum}
\longrightarrow
\text{estado real do operador}.
$$

Logo, as duas descrições não permanecem paralelas. Elas são apresentações
distintas da mesma condição de admissibilidade. A distinção ponto a ponto
entre $b^{-k}$ e $n^{-1}$ continua preservada, exatamente como exige a
arquitetura oficial.

---

## 6. Estado real do carry

### 6.1. Espaço de estados

```lean
abbrev NativeCarryRealPlane := ℝ × ℝ
```

O estado vive em $\mathbb R^2$. Nenhuma estrutura complexa é necessária para
defini-lo, girá-lo, somá-lo ou detectar seu zero.

Fonte:
[`NativeCarryRealPlane`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean#L85).

### 6.2. Energia

```lean
def nativeCarryRealPlaneEnergy (u : NativeCarryRealPlane) : ℝ :=
  u.1 ^ 2 + u.2 ^ 2
```

Portanto, para $u=(x,y)$:

$$
E(u)=x^2+y^2.
$$

Fonte:
[`nativeCarryRealPlaneEnergy`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean#L88-L89).

### 6.3. Rotação

A direção unitária de ângulo $\theta$ é

$$
d(\theta)=(\cos\theta,\sin\theta).
$$

Equivalente matricialmente:

$$
d(\theta)
=
\begin{pmatrix}
\cos\theta & -\sin\theta\\
\sin\theta & \cos\theta
\end{pmatrix}
\begin{pmatrix}
1\\
0
\end{pmatrix}.
$$

O Lean prova:

$$
E(d(\theta))=1.
$$

Fonte:
[`nativeCarryRealDirection`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean#L92-L99).

### 6.4. Amostra deformada

Para $n>0$:

$$
u_{\sigma,t}(n)
=
n^{-\sigma}d(-t\log n).
$$

Ou, expandindo:

$$
\boxed{
u_{\sigma,t}(n)
=
n^{-\sigma}
\bigl(
\cos(-t\log n),
\sin(-t\log n)
\bigr).
}
$$

O código torna a função total em $\mathbb Z$ definindo $u_{\sigma,t}(n)=0$
para $n\le0$:

```lean
def nativeCarryRealPlaneSampleAt
    (sigma t : ℝ) (n : ℤ) : NativeCarryRealPlane :=
  if 0 < n then
    let amplitude := (n : ℝ) ^ (-sigma)
    let angle := -t * Real.log (n : ℝ)
    (amplitude * Real.cos angle, amplitude * Real.sin angle)
  else
    0
```

Fonte:
[`nativeCarryRealPlaneSampleAt`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean#L105-L113).

O estado já especializado na casca nativa é:

```lean
def nativeCarryRealPlaneSample
    (t : ℝ) (n : ℤ) : NativeCarryRealPlane :=
  nativeCarryRealPlaneSampleAt ((1 : ℝ) / 2) t n
```

Fonte:
[`nativeCarryRealPlaneSample`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean#L115-L118).

### 6.5. Energia da amostra

Para $n>0$:

$$
\begin{aligned}
E(u_{\sigma,t}(n))
&=
n^{-2\sigma}
\left(
\cos^2(-t\log n)+\sin^2(-t\log n)
\right)\\
&=
n^{-2\sigma}.
\end{aligned}
$$

Assim:

$$
\boxed{
E(u_{\sigma,t}(n))=n^{-2\sigma}.
}
$$

Fonte:
[`nativeCarryRealPlaneEnergy_sampleAt`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean#L136-L158).

Em $\sigma=\frac12$:

$$
\boxed{
E\left(u_{\frac12,t}(n)\right)=n^{-1}.
}
$$

Fonte:
[`nativeCarryRealPlaneEnergy_sample`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean#L164-L170).

### 6.6. Compatibilidade de massa

```lean
def NativeCarryRealPlaneMassCompatible
    (sigma t : ℝ) : Prop :=
  ∀ n : ℤ, 1 < n →
    nativeCarryRealPlaneEnergy
        (nativeCarryRealPlaneSampleAt sigma t n) =
      ((n : ℝ))⁻¹
```

O índice $n=1$ é excluído porque

$$
1^{-2\sigma}=1
$$

para todo $\sigma$; ele não consegue distinguir expoentes.

O Lean prova:

```lean
theorem nativeCarryRealPlaneMassCompatible_iff
    (sigma t : ℝ) :
    NativeCarryRealPlaneMassCompatible sigma t ↔
      sigma = (1 : ℝ) / 2
```

A direção de rigidez já é obtida usando $n=2$:

$$
2^{-2\sigma}=2^{-1}
\Longrightarrow
-2\sigma=-1
\Longrightarrow
\sigma=\frac12.
$$

A volta usa a identidade de energia para todo $n>1$.

Fontes:

- [`NativeCarryRealPlaneMassCompatible`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean#L177-L185);
- [`nativeCarryRealPlaneMassCompatible_iff`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean#L188-L206).

Consequência estrutural:

$$
\text{o tempo altera a direção, mas não participa da seleção radial.}
$$

---

## 7. O bracket aditivo

### 7.1. Segunda diferença centrada

Para uma função $f:\mathbb Z\to A$, com $A$ apenas um grupo comutativo
aditivo:

$$
\boxed{
\Delta_r^2 f(q)
=
f(q-r)-2f(q)+f(q+r).
}
$$

No Lean:

```lean
def centeredSecondDifference (f : ℤ → A) (center radius : ℤ) : A :=
  f (center - radius) - (2 • f center) + f (center + radius)
```

Fonte:
[`centeredSecondDifference`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Finite/Bracket.lean#L18-L19).

Interpretação:

- o bracket mede defeito de afinidade ou curvatura discreta;
- uma função afim tem segunda diferença zero;
- o operador local compara um centro com duas pernas simétricas;
- nenhuma multiplicação entre estados é necessária.

### 7.2. Bracket saturado

Para semialcance $h$:

$$
\boxed{
\mathcal B_h f(q)
=
\sum_{r=1}^{h}
\Delta_r^2f(q).
}
$$

No Lean:

```lean
def saturatedBracket (h : ℕ) (f : ℤ → A) (center : ℤ) : A :=
  ∑ radius ∈ Finset.Icc 1 h,
    centeredSecondDifference f center (radius : ℤ)
```

Fonte:
[`saturatedBracket`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Finite/Bracket.lean#L40-L42).

### 7.3. Naturalidade aditiva

Se $J:A\to B$ é aditivo, então aplicar $J$ depois da câmera é igual a aplicar
$J$ em cada amostra antes da câmera:

$$
J\bigl(\operatorname{Chart}_{c,M}(f)\bigr)
=
\operatorname{Chart}_{c,M}(J\circ f).
$$

Essa identidade é a razão formal pela qual uma mudança fiel de recipiente não
altera o resultante.

Fonte:
[`map_nativeCarryFiniteSaturatedChart`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean#L54-L63).

---

## 8. Geometria completa da câmera finita

### 8.1. Semialcance, semente e centros

Para uma câmera natural $c$:

$$
h_c=\left\lfloor\frac{c-1}{2}\right\rfloor.
$$

A semente positiva é

$$
S_c(f)=\sum_{n=1}^{h_c}f(n).
$$

O centro de índice $k$, começando em zero, é

$$
q_{c,k}=c(k+1).
$$

Fontes:

- [`seedSum`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Genuine/CpFiniteChart.lean#L41-L43);
- [`alignedCenter`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Genuine/CpFiniteChart.lean#L45-L47).

### 8.2. Definição Lean

```lean
def nativeCarryFiniteSaturatedChart
    {A : Type*} [AddCommGroup A]
    (c M : ℕ) (f : ℤ → A) : A :=
  (∑ n ∈ Finset.Icc (1 : ℤ)
      (halfRange c : ℤ), f n) +
    ∑ k ∈ Finset.range M,
      saturatedBracket
        (halfRange c) f
        (alignedCenter c k)
```

Fonte:
[`nativeCarryFiniteSaturatedChart`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean#L43-L50).

### 8.3. Fórmula totalmente expandida

Substituindo a definição do bracket:

$$
\boxed{
\begin{aligned}
\operatorname{Chart}_{c,M}(f)
&=
\sum_{n=1}^{h_c}f(n)\\
&\quad+
\sum_{k=0}^{M-1}
\sum_{r=1}^{h_c}
\left[
f\bigl(c(k+1)-r\bigr)
-2f\bigl(c(k+1)\bigr)
+f\bigl(c(k+1)+r\bigr)
\right].
\end{aligned}
}
$$

Para o estado real:

$$
\boxed{
\begin{aligned}
R_{c,M}(\sigma,t)
&=
\sum_{n=1}^{h_c}u_{\sigma,t}(n)\\
&\quad+
\sum_{k=0}^{M-1}
\sum_{r=1}^{h_c}
\Bigl[
u_{\sigma,t}\bigl(c(k+1)-r\bigr)
-2u_{\sigma,t}\bigl(c(k+1)\bigr)\\
&\hspace{10.5em}
+u_{\sigma,t}\bigl(c(k+1)+r\bigr)
\Bigr].
\end{aligned}
}
$$

Essa é a fórmula do resultante finito usado no predicado terminal do Lean.

### 8.4. Coordenadas expandidas

Escreva

$$
u_{\sigma,t}(n)=\bigl(x_{\sigma,t}(n),y_{\sigma,t}(n)\bigr),
$$

com

$$
x_{\sigma,t}(n)=n^{-\sigma}\cos(-t\log n),
$$

$$
y_{\sigma,t}(n)=n^{-\sigma}\sin(-t\log n).
$$

Então

$$
R_{c,M}(\sigma,t)
=
\bigl(
R_{c,M}^{(x)}(\sigma,t),
R_{c,M}^{(y)}(\sigma,t)
\bigr),
$$

onde cada coordenada recebe exatamente o mesmo stencil:

$$
\begin{aligned}
R_{c,M}^{(x)}
&=
\sum_{n=1}^{h_c}x(n)
+
\sum_{k=0}^{M-1}
\sum_{r=1}^{h_c}
\left[
x(q_{c,k}-r)-2x(q_{c,k})+x(q_{c,k}+r)
\right],
\end{aligned}
$$

$$
\begin{aligned}
R_{c,M}^{(y)}
&=
\sum_{n=1}^{h_c}y(n)
+
\sum_{k=0}^{M-1}
\sum_{r=1}^{h_c}
\left[
y(q_{c,k}-r)-2y(q_{c,k})+y(q_{c,k}+r)
\right].
\end{aligned}
$$

### 8.5. Carta real no Lean

```lean
def nativeCarryRealPlaneFiniteChartAt
    (c M : ℕ) (sigma t : ℝ) : NativeCarryRealPlane :=
  nativeCarryFiniteSaturatedChart c M
    (nativeCarryRealPlaneSampleAt sigma t)
```

A versão já crítica é:

```lean
def nativeCarryRealPlaneFiniteChart
    (c M : ℕ) (t : ℝ) : NativeCarryRealPlane :=
  nativeCarryRealPlaneFiniteChartAt c M ((1 : ℝ) / 2) t
```

Fontes:

- [`nativeCarryRealPlaneFiniteChartAt`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean#L212-L215);
- [`nativeCarryRealPlaneFiniteChart`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean#L218-L221).

### 8.6. Exemplo: câmera 3

Para $c=3$:

$$
h_3=1,
$$

e

$$
\boxed{
R_{3,M}(\sigma,t)
=
u_{\sigma,t}(1)
+
\sum_{j=1}^{M}
\left[
u_{\sigma,t}(3j-1)
-2u_{\sigma,t}(3j)
+u_{\sigma,t}(3j+1)
\right].
}
$$

Como os blocos são completos e adjacentes, a carta de câmera 3 também pode
ser escrita:

$$
R_{3,M}(\sigma,t)
=
\sum_{n=1}^{3M+1}u_{\sigma,t}(n)
-3\sum_{j=1}^{M}u_{\sigma,t}(3j).
$$

### 8.7. Exemplo: câmera 5

Para $c=5$:

$$
h_5=2.
$$

Logo:

$$
\begin{aligned}
R_{5,M}
&=
u(1)+u(2)\\
&\quad+
\sum_{j=1}^{M}
\Bigl(
\Delta_1^2u(5j)+\Delta_2^2u(5j)
\Bigr).
\end{aligned}
$$

### 8.8. Forma por prefixo para câmera prima ímpar

Quando $c$ é primo ímpar, o Lean identifica a carta saturada com a carta finita
residual e prova:

$$
\boxed{
\operatorname{Chart}_{c,M}(f)
=
\sum_{n=1}^{cM+h_c}f(n)
-c\sum_{j=1}^{M}f(cj).
}
$$

Fontes:

- [`bracket_eq_saturatedBracket`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Genuine/CpBracketPairing.lean#L130-L142);
- [`nativeCarryFiniteSaturatedChart_eq_finiteChart`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean#L68-L78);
- [`finiteChart_eq_positiveIntervalSum_sub_p_mul_centerSum`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Genuine/CpFiniteChart.lean#L246-L258).

Primalidade é usada nessa identificação formal com a carta residual. Ela não
é necessária para definir a câmera aditiva nativa nem para o teorema terminal
de fatoração de zeros.

---

## 9. Casos de câmera que precisam ser distinguidos

| Câmera | $h_c$ no Lean | Situação da carta nativa |
|---:|---:|---|
| $c=0$ | $0$ | carta degenerada |
| $c=1$ | $0$ | carta degenerada |
| $c=2$ | $0$ | carta genérica `Cp` degenerada |
| $c=2h+1\ge3$ ímpar | $h$ | janela simétrica com $2h+1=c$ posições |
| $c\ge4$ par | $c/2-1$ | detector aditivo válido, com bloco de largura $c-1$ |
| $c$ primo ímpar | $(c-1)/2$ | além da carta nativa, há identificação formal com `Cp.finiteChart` |

### 9.1. O quantificador “toda câmera”

O teorema terminal realmente recebe:

```lean
camera : ℕ
```

e não exige primalidade, paridade ou limite inferior.

Esse quantificador é uma única lei universal:

$$
\forall c\in\mathbb N,\ \forall\sigma,t\in\mathbb R,\qquad
\operatorname{Zero}_c(\sigma,t)
\iff
\left(\sigma=\frac12\right)\land\operatorname{Resonance}_c(t).
$$

Não são provas isoladas, uma para cada largura. O kernel elaborou
simultaneamente uma regra válida para câmera par, ímpar, prima, composta e
também para os casos degenerados da definição total.

Combinada com `branchNormSq_eq_one_base_independent` e
`positionalCarryMassCompatible_iff_realEnergyCompatible`, essa universalidade
mostra que a câmera não determina o locus radial. A câmera é uma carta de
observação sobre um domínio quadrático global já fixado pelo carry.

A invariância exigida pela teoria não é a igualdade definicional entre todos
os somatórios brutos. Ela é a independência do domínio, da lei terminal e do
representante canônico normalizado. Exigir uma identidade literal entre
predicados brutos com fórmulas locais diferentes responderia a outra pergunta
e não é uma obrigação pendente do operador.

### 9.2. A câmera 2 usada no scanner numérico

O scanner anexado não usa a carta genérica `Cp` quando `camera == 2`. Ele usa
uma especialização $C_2$ própria:

- semente $u(1)$;
- raio único $r=1$;
- centros $4,8,12,\ldots,4M$.

Sua fórmula é:

$$
\boxed{
R^{C_2}_{M}(t)
=
u_{\frac12,t}(1)
+
\sum_{j=1}^{M}
\left[
u_{\frac12,t}(4j-1)
-2u_{\frac12,t}(4j)
+u_{\frac12,t}(4j+1)
\right].
}
$$

Essa câmera $C_2$ numérica é não degenerada e corresponde à geometria binária
especial do projeto. Ela **não é literalmente** a instância `camera = 2` de
`nativeCarryFiniteSaturatedChart`, porque nessa família

$$
h_2=\left\lfloor\frac{2-1}{2}\right\rfloor=0.
$$

Consequência documental:

> os resultados numéricos da câmera 2 devem ser citados como evidência da
> especialização $C_2$, não como execução literal da instância genérica
> `nativeCarryFiniteSaturatedChart 2`.

Para as câmeras numéricas $c>2$, o script usa

$$
h_c=\left\lfloor\frac{c-1}{2}\right\rfloor
$$

e centros $cj$, de acordo com a fórmula genérica.

### 9.3. Por que a câmera 3 aparece depois

A câmera $3$ não é a origem do fenômeno. Na apresentação analítica histórica,
o Lean primeiro prova a compatibilidade ponto a ponto das câmeras normalizadas:

```lean
theorem cpGenuineQuotient_eq_cpGenuineQuotient ...
```

e, na roupa real-espectral:

```lean
theorem realSpectralCamera_prime_independent ...
```

Somente depois define:

```lean
def genuineContinuation (s : ℂ) : ℂ :=
  cpGenuineQuotient 3 s
```

Fontes:

- [`CpGenuineCompatibility.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpGenuineCompatibility.lean), com
  `cpGenuineQuotient_eq_cpGenuineQuotient`;
- [`CpRealSpectralOperator.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpRealSpectralOperator.lean), com
  `realSpectralCamera_prime_independent`.

Na nomenclatura oficial:

| Nome histórico | Nome oficial planejado |
|---|---|
| `cpGenuineQuotient` | `normalizedBracketChart` |
| `genuineContinuation` | `canonicalCarryContinuation` |
| `cpGenuineQuotient_eq_cpGenuineQuotient` | `normalizedBracketChart_camera_independent` |

Assim, o número $3$ é um representante escolhido para escrever o objeto comum
depois da equivalência; ele não privilegia uma base, não causa a ressonância e
não restringe a lei universal do operador real.

---

## 10. Zero finito e energia visível

### 10.1. Energia do resultante

Se

$$
R_{c,M}=(X_{c,M},Y_{c,M}),
$$

a energia visível do resultante é:

$$
E_{\mathrm{vis}}(R_{c,M})
=
X_{c,M}^2+Y_{c,M}^2.
$$

O Lean prova:

$$
\boxed{
E_{\mathrm{vis}}(R_{c,M})=0
\iff
R_{c,M}=(0,0).
}
$$

Fontes:

- [`nativeCarryRealPlaneEnergy_eq_zero_iff`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean#L245-L271);
- [`nativeCarryRealPlaneFiniteChart_energy_eq_zero_iff`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean#L278-L283).

### 10.2. Zero finito admissível

```lean
def NativeCarryRealPlaneAdmissibleFiniteZero
    (c M : ℕ) (sigma t : ℝ) : Prop :=
  NativeCarryRealPlaneMassCompatible sigma t ∧
    nativeCarryRealPlaneEnergy
      (nativeCarryRealPlaneFiniteChartAt c M sigma t) = 0
```

O Lean prova:

$$
\boxed{
\begin{aligned}
\operatorname{AdmissibleFiniteZero}(c,M,\sigma,t)
\iff{}&
\sigma=\frac12\\
&{}\land
E_{\mathrm{vis}}
\left(
R_{c,M}\left(\frac12,t\right)
\right)=0.
\end{aligned}
}
$$

Fontes:

- [`NativeCarryRealPlaneAdmissibleFiniteZero`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean#L290-L295);
- [`nativeCarryRealPlaneAdmissibleFiniteZero_iff`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean#L302-L323).

### 10.3. Energia interna não é energia visível

Se a câmera soma vetores $v_1,\ldots,v_N$, existem duas quantidades diferentes:

$$
E_{\mathrm{vis}}
=
\left\|
\sum_{j=1}^{N}v_j
\right\|^2,
$$

e

$$
E_{\mathrm{int}}
=
\sum_{j=1}^{N}\|v_j\|^2.
$$

Pode ocorrer:

$$
\sum_{j=1}^{N}v_j=0
$$

enquanto

$$
\sum_{j=1}^{N}\|v_j\|^2>0.
$$

Isso não é perda de energia. É cancelamento vetorial:

- o observador do resultante vê zero;
- as contribuições internas continuam não nulas;
- a energia individual pode permanecer presente, mas invisível na síntese
  escalar ou vetorial final.

O núcleo Lean usa $E_{\mathrm{vis}}$ para detectar o zero do resultante. O
campo `total_energy` dos testes Python mede uma soma interna de energias e é um
diagnóstico diferente.

---

## 11. Passagem ao limite

### 11.1. Fechamento bruto da câmera

```lean
def NativeCarryRealOperatorBoundaryClosesAt
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  Tendsto
    (fun cutoff : ℕ =>
      nativeCarryRealPlaneFiniteChartAt camera cutoff sigma time)
    atTop (nhds 0)
```

Em notação:

$$
\boxed{
\operatorname{BoundaryClosesAt}(c,\sigma,t)
\iff
R_{c,M}(\sigma,t)\to(0,0).
}
$$

Fonte:
[`NativeCarryRealOperatorBoundaryClosesAt`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean#L41-L46).

Esse é um limite em $\mathbb R^2$. Ele equivale ao fechamento simultâneo das
duas coordenadas reais.

Não é exigido que algum cutoff finito produza zero exato.

### 11.2. Ressonância nativa

```lean
def IsNativeCarryRealOperatorResonance
    (camera : ℕ) (time : ℝ) : Prop :=
  NativeCarryRealOperatorBoundaryClosesAt
    camera ((1 : ℝ) / 2) time
```

Logo:

$$
\boxed{
\operatorname{Resonance}_c(t)
\iff
R_{c,M}\left(\frac12,t\right)\to(0,0).
}
$$

Fonte:
[`IsNativeCarryRealOperatorResonance`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean#L52-L55).

### 11.3. Zero do operador real de carry

```lean
def IsNativeCarryRealOperatorZero
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  NativeCarryRealPlaneMassCompatible sigma time ∧
    NativeCarryRealOperatorBoundaryClosesAt camera sigma time
```

Em notação:

$$
\boxed{
\operatorname{Zero}_c(\sigma,t)
\iff
\operatorname{MassCompatible}(\sigma,t)
\land
\operatorname{BoundaryClosesAt}(c,\sigma,t).
}
$$

Fonte:
[`IsNativeCarryRealOperatorZero`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean#L65-L68).

A compatibilidade de massa é parte do domínio do operador. Ela não é
inferida depois de observar um cancelamento bruto.

---

## 12. Teorema de Fatoração do Conjunto de Zeros do Operador Real de Carry

**Nome acadêmico:** Real Carry Operator Zero-Set Factorization Theorem.

**Identificador oficial planejado:** `NCG-OPR-004`.

O nome Lean histórico permanece abaixo para permitir localização direta no
repositório de proveniência.

### 12.1. Enunciado

```lean
theorem isNativeCarryRealOperatorZero_iff
    (camera : ℕ) (sigma time : ℝ) :
    IsNativeCarryRealOperatorZero camera sigma time ↔
      sigma = (1 : ℝ) / 2 ∧
        IsNativeCarryRealOperatorResonance camera time
```

Fonte:
[`isNativeCarryRealOperatorZero_iff`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean#L79-L97).

Em notação:

$$
\boxed{
\operatorname{Zero}_c(\sigma,t)
\iff
\left(\sigma=\frac12\right)
\land
\operatorname{Resonance}_c(t).
}
$$

Ou:

$$
\boxed{
Z_c
=
\left\{\frac12\right\}\times\mathcal R_c.
}
$$

### 12.2. Prova Lean completa

```lean
theorem isNativeCarryRealOperatorZero_iff
    (camera : ℕ) (sigma time : ℝ) :
    IsNativeCarryRealOperatorZero camera sigma time ↔
      sigma = (1 : ℝ) / 2 ∧
        IsNativeCarryRealOperatorResonance camera time := by
  unfold IsNativeCarryRealOperatorZero
    IsNativeCarryRealOperatorResonance
  constructor
  · rintro ⟨hmass, hclose⟩
    have hsigma : sigma = (1 : ℝ) / 2 :=
      (nativeCarryRealPlaneMassCompatible_iff sigma time).1 hmass
    subst sigma
    exact ⟨rfl, hclose⟩
  · rintro ⟨hsigma, hresonance⟩
    subst sigma
    exact
      ⟨(nativeCarryRealPlaneMassCompatible_iff
          ((1 : ℝ) / 2) time).2 rfl,
        hresonance⟩
```

### 12.3. Leitura da prova

Direção direta:

1. abra o zero em massa mais fechamento;
2. use `nativeCarryRealPlaneMassCompatible_iff`;
3. obtenha $\sigma=\frac12$;
4. substitua $\sigma$;
5. o fechamento restante é literalmente a ressonância.

Direção inversa:

1. receba $\sigma=\frac12$ e uma ressonância;
2. substitua $\sigma$;
3. reconstrua a compatibilidade de massa pela volta do `iff`;
4. reutilize o mesmo fechamento.

O teorema não é `Iff.rfl`, pois a equivalência

$$
\operatorname{MassCompatible}(\sigma,t)
\iff
\sigma=\frac12
$$

contém a rigidez quadrática real já provada. Depois dessa rigidez, a fatoração
final é uma composição curta e exata das definições.

### 12.4. O que não aparece na prova

Não aparecem:

- primalidade da câmera;
- paridade da câmera;
- parâmetro não real;
- identificação com qualquer função externa;
- Green;
- TFVD;
- Bessel;
- reconstrução;
- estado-fonte;
- realização auto-adjunta;
- hipótese de existência de ressonância.

---

## 13. Corolários formais

### 13.1. Confinamento radial

```lean
theorem nativeCarryRealOperatorZero_sigma_eq_half
    {camera : ℕ} {sigma time : ℝ}
    (hzero : IsNativeCarryRealOperatorZero camera sigma time) :
    sigma = (1 : ℝ) / 2
```

Fonte:
[`nativeCarryRealOperatorZero_sigma_eq_half`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean#L103-L107).

### 13.2. Ausência de zero do operador fora da casca

```lean
theorem nativeCarryRealOperatorZero_ne_of_sigma_ne_half
    {camera : ℕ} {sigma time : ℝ}
    (hoff : sigma ≠ (1 : ℝ) / 2) :
    ¬ IsNativeCarryRealOperatorZero camera sigma time
```

Fonte:
[`nativeCarryRealOperatorZero_ne_of_sigma_ne_half`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean#L110-L115).

### 13.3. Especialização da câmera 3

Esta especialização é uma compatibilidade de nomes históricos. Ela não
seleciona a câmera responsável pelo fenômeno: como mostrado na Seção 9.3, o
representante $3$ só é escolhido depois da equivalência canônica das câmeras
normalizadas.

O novo fechamento arbitrário, especializado em câmera 3, é
definicionalmente o predicado antigo:

```lean
@[simp] theorem nativeCarryRealOperatorBoundaryClosesAt_three
    (sigma time : ℝ) :
    NativeCarryRealOperatorBoundaryClosesAt 3 sigma time ↔
      NativeCarryRealPlaneBoundaryClosesAt sigma time :=
  Iff.rfl
```

Fonte:
[`nativeCarryRealOperatorBoundaryClosesAt_three`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean#L121-L125).

O zero da câmera 3 coincide definicionalmente com o fechamento admissível
antigo:

```lean
@[simp] theorem isNativeCarryRealOperatorZero_three_iff
    (sigma time : ℝ) :
    IsNativeCarryRealOperatorZero 3 sigma time ↔
      NativeCarryRealPlaneAdmissibleBoundaryClosesAt sigma time :=
  Iff.rfl
```

Fonte:
[`isNativeCarryRealOperatorZero_three_iff`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean#L131-L135).

---

## 14. Escopo lógico exato e invariância de câmera

| Afirmação | Estado auditado |
|---|---|
| Todo zero do operador real de carry tem $\sigma=\frac12$ | provado |
| Fora de $\sigma=\frac12$ o operador real de carry não zera | provado |
| O conjunto de zeros fatoriza como $\{1/2\}\times\mathcal R_c$ | provado |
| A lei terminal vale para qualquer `camera : ℕ` | provado |
| A rigidez quadrática vale para toda base $b>1$ | provado |
| Bases distintas possuem o mesmo domínio quadrático admissível | provado |
| O domínio posicional e o domínio de energia real são equivalentes | provado no PR #18 |
| A câmera finita aditiva exige primalidade | falso; a definição não exige |
| As câmeras normalizadas do atlas recuperam um representante canônico comum | provado |
| A câmera $3$ é escolhida somente depois da equivalência canônica | provado |
| O empacotamento real–analítico cria ou desloca zeros | falso |
| O bracket escolhe novamente $\sigma$ por cancelamento | falso |
| O tempo altera a energia do estado | falso |
| Energia interna positiva impede resultante zero | falso |

### 14.1. O fenômeno é global

A invariância de câmera resulta da composição de três teoremas, e não de uma
hipótese informal:

1. `branchNormSq_eq_one_base_independent` identifica o mesmo locus admissível
   para quaisquer bases $b,d>1$;
2. `positionalCarryMassCompatible_iff_realEnergyCompatible` transporta esse
   locus para o domínio do estado real;
3. `isNativeCarryRealOperatorZero_iff` quantifica universalmente sobre
   `camera : ℕ` e fatoriza o zero pela mesma casca $\sigma=\frac12$.

No atlas analítico normalizado,
`cpGenuineQuotient_eq_cpGenuineQuotient` e
`realSpectralCamera_prime_independent` identificam o representante comum antes
da escolha convencional da câmera $3$.

Portanto:

$$
\boxed{
\text{a câmera muda a carta local de observação, não o fenômeno global.}
}
$$

Isso engloba a lei radial para bases pares, ímpares, primas e compostas. Bases
primas podem formar um atlas mínimo não redundante; elas não criam a rigidez e
não recebem privilégio causal.

### 14.2. Igualdade bruta de fórmulas não é a noção de invariância

Uma câmera binária especial, uma janela ímpar balanceada e uma largura par
genérica não possuem necessariamente o mesmo somatório escrito termo a termo.
Exigir

$$
\operatorname{BoundaryClosesAt}_c
\equiv
\operatorname{BoundaryClosesAt}_d
$$

como igualdade definicional de implementações trocaria a pergunta. A teoria
identifica:

- o domínio quadrático comum;
- a lei universal de fatoração;
- o representante normalizado comum;
- as apresentações fiéis do mesmo operador.

Essa é a invariância necessária e já fechada. A igualdade textual de todos os
predicados brutos não é uma premissa omitida e não deve ser reaberta como
dívida retroativa.

### 14.3. A componente temporal não é uma lacuna do teorema

O teorema terminal separa exatamente:

$$
\text{zero}
=
\text{casca radial rígida}
\times
\text{ressonância temporal}.
$$

Ele não foi formulado para enumerar os tempos de ressonância; ele os isola no
predicado correto de fechamento. Investigar uma enumeração, uma taxa de
convergência ou uma realização adicional é uma pergunta posterior, não uma
premissa ausente da fatoração já elaborada.

---

## 15. Domínio e fechamento: distinção de tipo, não pendência

O fechamento de bordo é:

$$
\operatorname{BoundaryClosesAt}(c,\sigma,t).
$$

O zero completo do operador é:

$$
\operatorname{MassCompatible}(\sigma,t)
\land
\operatorname{BoundaryClosesAt}(c,\sigma,t).
$$

A compatibilidade de massa é o domínio herdado do carry. Ela acompanha o
operador em qualquer mudança fiel de apresentação. Apagá-la não simplifica o
mesmo objeto; define outro predicado.

Essa distinção deve ser preservada sem transformá-la em uma nova obrigação:

- o confinamento terminal já está fechado;
- o crosswalk entre as apresentações transporta o fechamento;
- a identidade completa dos predicados conserva também o domínio;
- Green, pencils, TFVD, Bessel, estado-fonte e reconstruções pertencem a rotas
  históricas ou extensões e não entram na menor cadeia oficial.

Na arquitetura oficial, as mudanças abaixo são explicitamente proibidas sem
uma nova assinatura:

- trocar o predicado de zero;
- apagar a compatibilidade de energia;
- identificar fechamento bruto com zero completo;
- usar um guardrail ou uma interface como se fosse uma construção.

Essas regras protegem o teorema já provado; elas não anunciam trabalho
matemático faltante.

---

## 16. Apresentações real e analítica do mesmo operador

O objeto chamado historicamente de “Primitivo” é a apresentação real em
$\mathbb R^2$. Na arquitetura oficial, o adjetivo não será usado: haverá
somente o **operador real de carry** e sua **apresentação analítica
canônica**.

### 16.1. O mapa de empacotamento

O mapa

$$
J:\mathbb R^2\to\mathbb C,
\qquad
J(x,y)=x+iy,
$$

é usado apenas como recipiente de duas coordenadas:

```lean
def nativeCarryRealPlaneComplexPackaging :
    NativeCarryRealPlane →+ ℂ
```

Fonte:
[`nativeCarryRealPlaneComplexPackaging`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneComplexPackaging.lean#L26-L30).

O Lean prova que:

1. $J$ é aditivo;
2. $J$ é injetivo;
3. `Complex.normSq (J u) = nativeCarryRealPlaneEnergy u`;
4. $J$ comuta com a câmera finita;
5. $J$ preserva o predicado de zero nas duas direções.

Fontes:

- [`nativeCarryRealPlaneComplexPackaging_injective`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneComplexPackaging.lean#L41-L46);
- [`normSq_nativeCarryRealPlaneComplexPackaging`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneComplexPackaging.lean#L49-L55);
- [`nativeCarryFiniteSaturatedChart_zero_iff_packaged_zero`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneComplexPackaging.lean#L76-L101);
- [`nativeCarryRealPlaneComplexPackaging_eq_finiteChart`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneComplexPackaging.lean#L119-L142);
- [`nativeCarryRealPlaneFiniteChartAt_zero_iff_packaged_zero`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneComplexPackaging.lean#L148-L178).

Conclusão finita:

$$
R_{c,M}(\sigma,t)=0
\iff
J\bigl(R_{c,M}(\sigma,t)\bigr)=0.
$$

Nenhum zero é criado, removido ou deslocado pelo empacotamento.

### 16.2. O representante canônico vem antes da câmera 3

As cartas analíticas de câmera são normalizadas e identificadas antes da
escolha de um representante:

$$
\operatorname{NormalizedChart}_p(s)
=
\operatorname{NormalizedChart}_q(s).
$$

Historicamente, essa igualdade aparece em
`cpGenuineQuotient_eq_cpGenuineQuotient`. Somente depois dela o código define
`genuineContinuation` usando a câmera $3$. A arquitetura oficial renomeará os
objetos para `normalizedBracketChart` e `canonicalCarryContinuation`.

Logo:

$$
\boxed{
\text{a câmera }3\text{ nomeia o representante comum; ela não produz o objeto.}
}
$$

### 16.3. Crosswalk no limite integrado

O conteúdo originado no PR #16 foi integrado novamente pela CI por meio do
[PR #19](https://github.com/thiagomassensini/primos/pull/19) e incorporado ao
`main`. Dentro do domínio analítico comum, o Lean prova:

```lean
theorem nativeCarryRealBoundaryClosure_iff_genuineContinuation_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    NativeCarryRealOperatorBoundaryClosesAt 3 s.re s.im ↔
      genuineContinuation s = 0
```

Fontes da prova original, preservadas por commit:

- [`nativeCarryRealPlaneComplexPackaging_sampleAt_eq_dirichletTerm`](https://github.com/thiagomassensini/primos/blob/19e01d8018fb182c08005be4dd294a382931ccf9/CPFormal/Analytic/CpGenuineNativeRealBoundaryCrosswalk.lean#L42-L69);
- [`nativeCarryRealPlaneComplexPackaging_finiteChartAt_eq_dirichlet`](https://github.com/thiagomassensini/primos/blob/19e01d8018fb182c08005be4dd294a382931ccf9/CPFormal/Analytic/CpGenuineNativeRealBoundaryCrosswalk.lean#L75-L135);
- [`genuineContinuation_zero_to_nativeCarryRealBoundaryClosure`](https://github.com/thiagomassensini/primos/blob/19e01d8018fb182c08005be4dd294a382931ccf9/CPFormal/Analytic/CpGenuineNativeRealBoundaryCrosswalk.lean#L141-L208);
- [`nativeCarryRealBoundaryClosure_to_genuineContinuation_zero`](https://github.com/thiagomassensini/primos/blob/19e01d8018fb182c08005be4dd294a382931ccf9/CPFormal/Analytic/CpGenuineNativeRealBoundaryCrosswalk.lean#L213-L275);
- [`nativeCarryRealBoundaryClosure_iff_genuineContinuation_zero`](https://github.com/thiagomassensini/primos/blob/19e01d8018fb182c08005be4dd294a382931ccf9/CPFormal/Analytic/CpGenuineNativeRealBoundaryCrosswalk.lean#L281-L289).

Checkpoint integrado:
[`CpGenuineNativeRealBoundaryCrosswalk.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpGenuineNativeRealBoundaryCrosswalk.lean).

O crosswalk identifica o fechamento nas duas apresentações. O predicado
analítico completo deve conservar o mesmo domínio:

```lean
def IsCanonicalCarryOperatorZero (s : ℂ) : Prop :=
  RealCarryEnergyCompatible s.re s.im ∧
    canonicalCarryContinuation s = 0
```

Então, no domínio comum, a composição correta é:

$$
\begin{aligned}
\operatorname{IsRealCarryOperatorZero}(3,\sigma,t)
&\iff
\operatorname{RealEnergyCompatible}(\sigma,t)
\land
\operatorname{CanonicalContinuation}(\sigma,t)=0\\
&\iff
\operatorname{IsCanonicalCarryOperatorZero}(\sigma,t).
\end{aligned}
$$

Na arquitetura oficial:

- `NCG-EQV-007` é o **Boundary Representation Theorem**, com origem verde no
  PR #19;
- `NCG-EQV-008` será a **Operator Presentation Identity**, obtida por
  composição e retenção do domínio no port;
- o estado “port pendente” do novo repositório não rebaixa a prova histórica
  nem cria uma obrigação para o confinamento.

### 16.4. Regra de linguagem

Não existem duas espécies de zero.

Há:

1. um domínio quadrático herdado do carry;
2. um fechamento do operador;
3. duas codificações fiéis do mesmo resultante.

`BoundaryClosesAt` nomeia o fechamento. O zero completo leva o domínio junto.
Empacotar as coordenadas em $\mathbb C$ não cria um “zero escalar” separado do
“zero real”.

---

## 17. Interpretação espectral real

O tempo entra somente pela rotação:

$$
u_{\frac12,t}(n)
=
n^{-1/2}R(-t\log n)e_1.
$$

Cada inteiro carrega uma frequência logarítmica $\log n$.

Assim:

- $t$ é um parâmetro real de evolução;
- a amplitude $n^{-1/2}$ é fixa;
- a direção gira com velocidade $\log n$;
- o bracket sintetiza as fases em cada câmera;
- uma ressonância é um tempo em que o resultante de bordo fecha.

O repositório possui módulos adicionais para:

- órbita de fase logarítmica;
- gerador diagonal finito;
- gerador maximal infinito;
- grupo unitário;
- limiar de espectro contínuo;
- pencils e relações de bordo.

Esses módulos refinam a interpretação espectral, mas não entram no corpo da
prova `isNativeCarryRealOperatorZero_iff`.

Uma observação formal importante é que a massa crítica por coordenada é
harmônica:

$$
\left\|u_{\frac12,t}(n)\right\|^2=\frac1n.
$$

Por isso, o estado crítico infinito não é um vetor ordinário de $\ell^2$; ele
é tratado como estado generalizado no limiar contínuo nas extensões
espectrais.

---

## 18. Cadeia oficial e corpo curto do teorema terminal

### 18.1. Ordem lógica oficial

1. representação posicional;
2. decomposição quociente–resíduo e profundidade;
3. probabilidade uniforme do evento de carry;
4. massa $b^{-k}$;
5. amplitude $b^{-k/2}$;
6. rigidez quadrática $\sigma=\frac12$;
7. crosswalk para o domínio de energia real;
8. estado real girante;
9. segunda diferença e bracket;
10. câmera saturada e resultantes finitos;
11. fechamento no limite;
12. zero como domínio mais fechamento;
13. fatoração do conjunto de zeros;
14. representante analítico comum das câmeras;
15. identidade das apresentações.

### 18.2. Corpo curto do teorema terminal

| Passo | Declaração |
|---|---|
| Estado real | `nativeCarryRealPlaneSampleAt` |
| Energia | `nativeCarryRealPlaneEnergy_sampleAt` |
| Domínio | `NativeCarryRealPlaneMassCompatible` |
| Rigidez | `nativeCarryRealPlaneMassCompatible_iff` |
| Carta | `nativeCarryRealPlaneFiniteChartAt` |
| Fechamento | `NativeCarryRealOperatorBoundaryClosesAt` |
| Ressonância | `IsNativeCarryRealOperatorResonance` |
| Zero | `IsNativeCarryRealOperatorZero` |
| Fatoração | `isNativeCarryRealOperatorZero_iff` |

O corpo curto usa diretamente a rigidez de energia real porque as costuras
anteriores já foram encapsuladas em teoremas. Isso não elimina a fundação do
carry: o PR #18 prova explicitamente

```text
PositionalCarryMassCompatible
  ↔ NativeCarryRealPlaneMassCompatible
  ↔ sigma = 1/2.
```

O fato de uma prova terminal reutilizar uma interface já fechada é compressão
formal, não paralelismo lógico e não circularidade.

O arquivo histórico importa módulos Green e de carrier para aliases antigos,
mas o corpo da fatoração não usa Green. A arquitetura oficial poda esses
imports e mantém apenas:

```text
QuadraticAmplitude
→ RealState
→ FiniteRealOperator
→ BoundaryOperator
→ ZeroSetFactorization.
```

---

## 19. Auditoria numérica anexada

### 19.1. Natureza do teste

O teste de ressonância congelada mede, para um único tempo fixo $t_*$:

$$
R_{c,M}(t_*)\to(0,0).
$$

O observável principal é a norma bruta:

$$
\|R_{c,M}(t_*)\|.
$$

O score normalizado é apenas secundário:

$$
\operatorname{score}_{c,M}
=
\frac{\|R_{c,M}\|^2}
{N_{c,M}E_{\mathrm{int},c,M}}.
$$

Uma queda do score, sozinha, não prova fechamento, porque o denominador cresce.
Por isso o script audita diretamente o vetor bruto.

### 19.2. Configuração

| Parâmetro | Valor |
|---|---|
| Tempo congelado | `30.42487612585898` |
| Câmeras | `2, 3, 5, 8, 9, 11, 12, 15` |
| Cutoffs | `262144, 524288, 1048576, 2097152` |
| Backend | CUDA |
| Estado | `float64` |
| Acumulação principal na CPU | `longdouble`, 63 bits de mantissa |
| Ordem de cauda configurada | $p=3/2$ |
| Auditoria de precisão | maior cutoff |
| Controle móvel | maior cutoff |
| Tempo total | `287.94 s` |
| Python | `3.12.12` |
| NumPy | `2.3.5` |

O arquivo `fixed_resonance(1).json` registra:

```text
status = FINITE_FROZEN_TIME_RESONANCE_AUDIT
schema = org.native-carry.primitive-fixed-resonance/v1
```

### 19.3. Modelo de cauda rotativa

Para cutoffs diádicos:

$$
\Delta_M=R_{2M}-R_M.
$$

O transporte esperado da cauda é:

$$
Q
=
2^{-p}R(-t_*\log2).
$$

O extrapolador vetorial é:

$$
\boxed{
L_M(p)
=
(I-Q)^{-1}
\left(
R_{2M}-QR_M
\right).
}
$$

Se

$$
R_M
=
L
+
M^{-p}R(-t_*\log M)a
+
o(M^{-p}),
$$

então $L_M(p)$ estima o limite $L$.

Para amplitude $n^{-1/2}$, a segunda diferença sugere uma cauda de ordem
$M^{-3/2}$: o stencil compra duas potências locais e a soma restante perde uma.
No teste, $p=3/2$ é um modelo assintótico configurado e também conferido pelos
dados; não é usado como substituto da norma bruta.

### 19.4. Resumo por cutoff

| $M$ | mínimo de $\|R\|$ | mediana de $\|R\|$ | máximo de $\|R\|$ | mediana de $\|L_M\|$ |
|---:|---:|---:|---:|---:|
| 262144 | $7.086\times10^{-9}$ | $2.264\times10^{-8}$ | $3.642\times10^{-8}$ | — |
| 524288 | $2.504\times10^{-9}$ | $8.004\times10^{-9}$ | $1.288\times10^{-8}$ | $1.625\times10^{-12}$ |
| 1048576 | $8.853\times10^{-10}$ | $2.829\times10^{-9}$ | $4.551\times10^{-9}$ | $1.485\times10^{-12}$ |
| 2097152 | $3.142\times10^{-10}$ | $1.002\times10^{-9}$ | $1.611\times10^{-9}$ | $1.497\times10^{-12}$ |

Ao dobrar $M$, a norma bruta cai por um fator próximo de

$$
2^{-3/2}\approx0.353553.
$$

### 19.5. Resumo por câmera no maior cutoff

| Câmera | $\|R_{c,2097152}\|$ | potência observada | $\|L_{\mathrm{fit}}\|$ | energia interna |
|---:|---:|---:|---:|---:|
| 2 | $3.142\times10^{-10}$ | 1.4972 | $1.222\times10^{-12}$ | 5.6174 |
| 3 | $6.436\times10^{-10}$ | 1.4992 | $1.575\times10^{-12}$ | 6.2432 |
| 5 | $8.975\times10^{-10}$ | 1.4989 | $1.402\times10^{-12}$ | 10.1529 |
| 8 | $7.753\times10^{-10}$ | 1.4996 | $5.306\times10^{-13}$ | 9.3599 |
| 9 | $1.239\times10^{-9}$ | 1.4987 | $2.621\times10^{-12}$ | 9.3922 |
| 11 | $1.376\times10^{-9}$ | 1.4986 | $2.870\times10^{-12}$ | 10.0227 |
| 12 | $1.106\times10^{-9}$ | 1.4994 | $9.966\times10^{-13}$ | 9.3435 |
| 15 | $1.611\times10^{-9}$ | 1.4993 | $2.273\times10^{-12}$ | 10.5867 |

O padrão observado é:

- norma bruta decaindo aproximadamente como $M^{-3/2}$;
- extrapolador vetorial estável perto de zero;
- energia interna claramente positiva;
- resultante próximo de zero apesar dessa energia interna;
- comportamento semelhante em câmeras primas e compostas testadas.

### 19.6. Calibração comum de raiz

As oito câmeras passaram pelos filtros internos do ajuste:

| Quantidade | Resultado |
|---|---:|
| média da raiz extrapolada | `30.424876125859488` |
| mediana | `30.424876125859505` |
| span entre câmeras | `0.000099 ns` |
| correção média sobre o alvo congelado | `+0.000509 ns` |
| menor cosseno tangente | `0.989259321` |

Essa concordância é condicionada ao modelo de cauda rotativa $M^{-3/2}$ e ao
tempo de referência usado no ajuste.

### 19.7. Controle móvel

O controle móvel procura o mínimo apenas no maior cutoff. Ele não entra no
teste formal de ressonância congelada.

No maior cutoff, os mínimos móveis ficaram entre aproximadamente

```text
30.424876125971
```

e

```text
30.424876126382.
```

O deslocamento finito observado foi de cerca de `0.11 ns` a `0.52 ns`,
dependendo da câmera. Isso é compatível com uma cauda ainda presente em cutoff
finito.

### 19.8. Energia presente e resultante oculto

No maior cutoff:

- as energias internas ficaram entre aproximadamente `5.62` e `10.59`;
- as normas dos resultantes ficaram entre aproximadamente
  $3.14\times10^{-10}$ e $1.61\times10^{-9}$;
- os scores ficaram na ordem de $10^{-26}$.

Isso ilustra exatamente:

$$
E_{\mathrm{int}}>0
\qquad\text{e}\qquad
E_{\mathrm{vis}}\approx0.
$$

O conteúdo continua presente nas componentes, mas o observador do resultante
vê cancelamento global.

### 19.9. Limites da evidência numérica

O teste não é uma prova do limite infinito. Ele fornece evidência finita
controlada.

Ele não prova:

- fechamento para todos os tempos;
- existência de infinitas ressonâncias;
- uma taxa uniforme em $c$;
- a instância Lean genérica da câmera 2;
- ausência de efeitos além dos cutoffs testados.

Também não é função desse experimento estabelecer a invariância de câmera. A
invariância estrutural vem dos teoremas Lean de independência da base, do
crosswalk dos domínios e da compatibilidade das cartas normalizadas. O teste
apenas confirma, em cutoffs finitos, que apresentações primas e compostas
seguem o mesmo alvo esperado.

Além disso:

- o tempo testado foi fornecido previamente;
- o ajuste usa a forma de cauda rotativa;
- funções elementares e estados principais usam `float64`;
- `longdouble` melhora a soma, mas não cria aritmética exata;
- o arquivo principal
  `native_carry_primitive_real_operator.py` não veio entre os anexos desta
  auditoria.

O JSON registra o hash esperado do operador:

```text
0006bcb248fa60216e93077cfc0d589d65eed49eddf6f916c680b1cf551c7b74
```

O helper anexado possui o hash correspondente ao JSON:

```text
acdde5473dc047aefa5e3927fd270267083f68bf8c462446f29f4f4ae5874028
```

Sem o arquivo do operador com o primeiro hash, a execução não é
integralmente reproduzível apenas com os anexos atuais.

### 19.10. Comando de reprodução

Com os três scripts corretos no mesmo diretório:

```bash
python3 primitive_fixed_resonance_test.py \
  --operator native_carry_primitive_real_operator.py \
  --helper primitive_cutoff_convergence_test.py \
  --cameras 2,3,5,8,9,11,12,15 \
  --cutoffs 262144,524288,1048576,2097152 \
  --target 30.42487612585898 \
  --tail-order 1.5 \
  --probe-step 0.000000001 \
  --backend cuda \
  --state-block 32768 \
  --gpu-batch 8 \
  --gpu-threads 256 \
  --precision-audit largest \
  --fit-points 3 \
  --mobile-control largest \
  --control-center 30.42487612585898 \
  --control-half-window 0.000000003 \
  --control-grid 0.0000000005 \
  --control-fit-step 0.0000000005 \
  --control-fit-iterations 3 \
  --cpu-neighborhood 2
```

Antes de executar:

```bash
sha256sum native_carry_primitive_real_operator.py
```

e confira se o hash coincide com o registrado.

---

## 20. O que pertence ao núcleo e o que é extensão

| Camada | Papel | Necessária para a fatoração terminal? |
|---|---|---|
| decomposição e profundidade | fundação posicional | sim na cadeia oficial; encapsulada antes do corpo terminal |
| probabilidade, massa e amplitude | origem e rigidez quadrática | sim na cadeia oficial |
| crosswalk dos domínios | liga carry e energia real | sim na arquitetura; verde no PR #18 |
| estado real | realização por inteiro | sim |
| energia $n^{-2\sigma}$ | separação radial/angular | sim |
| compatibilidade de energia | domínio do operador | sim |
| bracket saturado | câmera aditiva | sim, na definição do fechamento |
| limite vetorial | fechamento de bordo | sim |
| empacotamento em duas coordenadas | representação fiel | não para a fatoração; sim para a identidade das apresentações |
| continuação analítica canônica | representante comum das câmeras | não para a fatoração real; sim para a equivalência real–analítica |
| Green | fluxo e bordo | não |
| TFVD e retorno | reconstrução | não |
| Bessel e ledger | orçamento global | não |
| precompression | levantamento do estado | não |
| Cayley e auto-adjunção | estrutura de bordo | não |
| teste numérico | evidência finita | não |

Essas extensões podem responder perguntas mais fortes. Elas não são condições
retroativas para o teorema de fatoração já compilado.

---

## 21. Índice mínimo de declarações e costuras auditadas

### 21.1. Carry e rigidez

| Declaração | Arquivo |
|---|---|
| `positionalDecompositionAtDepth_existsUnique` | [`PositionalDecomposition.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Carry/PositionalDecomposition.lean) |
| `positionalDepth_factorization_existsUnique` | [`PositionalDecomposition.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Carry/PositionalDecomposition.lean) |
| `uniformCarryEvent_probability` | [`UniformCarryProbability.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Carry/UniformCarryProbability.lean) |
| `effectiveDepth_eq_centerDepth` | [`CpDepth.lean`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Carry/CpDepth.lean#L107-L118) |
| `criticalMass` | [`CpBranchWeight.lean`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Carry/CpBranchWeight.lean#L33-L35) |
| `criticalAmplitude` | [`CpBranchWeight.lean`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Carry/CpBranchWeight.lean#L37-L39) |
| `criticalAmplitude_sq_eq_mass` | [`CpBranchWeight.lean`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Carry/CpBranchWeight.lean#L59-L66) |
| `branchAmplitude_sq_eq_criticalMass_iff_of_one_lt` | [`CpPositionalCarryQuadraticRigidity.lean`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean#L44-L66) |
| `positionalCarryMassCompatible_iff` | [`CpPositionalCarryQuadraticRigidity.lean`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean#L80-L96) |
| `branchNormSq_eq_one_base_independent` | [`CpPositionalCarryQuadraticRigidity.lean`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean#L286-L295) |
| `positionalCarryMassCompatible_iff_realEnergyCompatible` | [`CpQuadraticDomainCrosswalk.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpQuadraticDomainCrosswalk.lean) |

### 21.2. Estado, bracket e câmera

| Declaração | Arquivo |
|---|---|
| `halfRange` | [`BalancedOffsets.lean`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Genuine/BalancedOffsets.lean#L16-L17) |
| `centeredSecondDifference` | [`Bracket.lean`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Finite/Bracket.lean#L18-L19) |
| `saturatedBracket` | [`Bracket.lean`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Finite/Bracket.lean#L40-L42) |
| `nativeCarryFiniteSaturatedChart` | [`CpNativeCarryRealPlaneBracket.lean`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean#L43-L50) |
| `map_nativeCarryFiniteSaturatedChart` | [`CpNativeCarryRealPlaneBracket.lean`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean#L54-L63) |
| `nativeCarryRealPlaneSampleAt` | [`CpNativeCarryRealPlaneBracket.lean`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean#L105-L113) |
| `nativeCarryRealPlaneEnergy_sampleAt` | [`CpNativeCarryRealPlaneBracket.lean`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean#L136-L158) |
| `nativeCarryRealPlaneMassCompatible_iff` | [`CpNativeCarryRealPlaneBracket.lean`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean#L188-L206) |
| `nativeCarryRealPlaneFiniteChartAt` | [`CpNativeCarryRealPlaneBracket.lean`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean#L212-L215) |
| `nativeCarryRealPlaneAdmissibleFiniteZero_iff` | [`CpNativeCarryRealPlaneBracket.lean`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean#L302-L323) |

### 21.3. Operador terminal

| Declaração | Arquivo |
|---|---|
| `NativeCarryRealOperatorBoundaryClosesAt` | [`CpNativeCarryRealOperatorConfinement.lean`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean#L41-L46) |
| `IsNativeCarryRealOperatorResonance` | [`CpNativeCarryRealOperatorConfinement.lean`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean#L52-L55) |
| `IsNativeCarryRealOperatorZero` | [`CpNativeCarryRealOperatorConfinement.lean`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean#L65-L68) |
| `isNativeCarryRealOperatorZero_iff` | [`CpNativeCarryRealOperatorConfinement.lean`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean#L79-L97) |
| `nativeCarryRealOperatorZero_sigma_eq_half` | [`CpNativeCarryRealOperatorConfinement.lean`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean#L103-L107) |
| `nativeCarryRealOperatorZero_ne_of_sigma_ne_half` | [`CpNativeCarryRealOperatorConfinement.lean`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean#L110-L115) |

### 21.4. Invariância de câmera e identidade das apresentações

| Declaração | Papel | Arquivo |
|---|---|---|
| `cpGenuineQuotient_eq_cpGenuineQuotient` | igualdade das cartas normalizadas antes da escolha da câmera $3$ | [`CpGenuineCompatibility.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpGenuineCompatibility.lean) |
| `realSpectralCamera_prime_independent` | mesma leitura no mesmo tempo real no atlas normalizado | [`CpRealSpectralOperator.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpRealSpectralOperator.lean) |
| `nativeCarryRealPlaneComplexPackaging_injective` | fidelidade do empacotamento | [`CpNativeCarryRealPlaneComplexPackaging.lean`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneComplexPackaging.lean#L41-L46) |
| `nativeCarryRealBoundaryClosure_iff_genuineContinuation_zero` | crosswalk bidirecional do fechamento no limite | [`CpGenuineNativeRealBoundaryCrosswalk.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpGenuineNativeRealBoundaryCrosswalk.lean) |

Na arquitetura oficial, esses resultados correspondem às famílias
`NCG-ANL-005`, `NCG-EQV-001`–`007` e à composição planejada
`NCG-EQV-008`.

---

## 22. Protocolo de leitura e verificação

Para localizar uma declaração:

```bash
rg -n 'nome_exato_da_declaracao' CPFormal -g '*.lean'
```

Para auditar marcadores proibidos:

```bash
bash scripts/static_audit.sh
```

Para elaborar todo o projeto:

```bash
lake build --wfail
```

Ordem recomendada de leitura:

1. `CPFormal/Carry/PositionalDecomposition.lean`;
2. `CPFormal/Carry/UniformCarryProbability.lean`;
3. `CPFormal/Carry/CpDepth.lean`;
4. `CPFormal/Carry/CpBranchWeight.lean`;
5. `CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean`;
6. `CPFormal/Analytic/CpQuadraticDomainCrosswalk.lean`;
7. `CPFormal/Finite/Bracket.lean`;
8. `CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean`;
9. `CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean`;
10. `CPFormal/Analytic/CpGenuineCompatibility.lean`;
11. `CPFormal/Analytic/CpNativeCarryRealPlaneComplexPackaging.lean`;
12. `CPFormal/Analytic/CpGenuineNativeRealBoundaryCrosswalk.lean`.

Essa ordem segue a cadeia auditada. Ela não começa pela câmera $3$ nem por uma
representação externa.

---

## 23. Glossário

### Carry

Transporte posicional que organiza os inteiros em profundidades.

### Profundidade

Número de camadas verticais do carry vistas por uma incidência.

### Massa

Peso quadrático associado à profundidade, $b^{-k}$.

### Amplitude

Raiz quadrática da massa, $b^{-k/2}$.

### Casca radial

Família de amplitudes determinada por um expoente $\sigma$. A única casca
compatível com a massa é $\sigma=\frac12$.

### Tempo

Parâmetro real que gira cada estado com frequência $\log n$.

### Bracket

Soma de segundas diferenças centradas que mede o defeito aditivo local.

### Câmera

Regra que escolhe semialcance, centros, sementes e brackets.

### Invariância de câmera

Independência do domínio quadrático e da lei terminal em relação à base ou à
largura escolhida, acompanhada pela identificação do representante analítico
normalizado. A câmera muda a carta local, não o fenômeno global.

### Resultante

Soma vetorial finita produzida pela câmera.

### Fechamento bruto

Convergência do resultante a zero, sem compatibilidade de massa na definição.

### Ressonância

Fechamento bruto já avaliado na casca $\sigma=\frac12$.

### Zero do operador real de carry

Compatibilidade de massa mais fechamento de bordo.

### Energia visível

Norma quadrática do resultante final.

### Energia interna

Soma das normas quadráticas das contribuições antes da síntese final.

---

## 24. Resumo de bolso

> A decomposição posicional determina a profundidade do carry. Sob resíduos
> uniformes, essa profundidade tem massa $b^{-k}$; sua amplitude quadrática é
> $b^{-k/2}$. Para toda base $b>1$, a compatibilidade da amplitude deformada
> $b^{-k\sigma}$ com a massa equivale a $\sigma=\frac12$. O PR #18 transporta
> formalmente esse mesmo domínio para o estado real
> $u_{\sigma,t}(n)=n^{-\sigma}(\cos(-t\log n),\sin(-t\log n))$, cuja energia é
> $n^{-2\sigma}$ e não depende de $t$. Uma câmera natural aplica brackets
> centrados e produz $R_{c,M}(\sigma,t)\in\mathbb R^2$. O zero completo é
> compatibilidade de energia mais fechamento de bordo. O Lean prova, em uma
> única lei universal,
> `IsNativeCarryRealOperatorZero camera sigma time ↔ sigma = 1/2 ∧
> IsNativeCarryRealOperatorResonance camera time`. Assim, a base ou a largura
> da câmera não altera o domínio nem a fatoração. As cartas normalizadas
> recuperam um representante canônico comum, e a câmera $3$ só é escolhida
> depois dessa equivalência. O PR #19 identifica o fechamento nas
> apresentações real e analítica; o domínio acompanha o transporte, portanto
> não existem duas espécies de zero. Green, TFVD, Bessel, estado-fonte,
> precompression e reconstruções são extensões, não obrigações retroativas.
> Os testes finitos ilustram a convergência e a energia oculta, sem substituir
> as provas do kernel.

---

## 25. Frase final

$$
\boxed{
\text{o que não muda quando a câmera muda é o fenômeno global:}
\quad
\text{domínio quadrático, casca }\sigma=\frac12
\text{ e operador canônico;}
\quad
\text{a câmera muda apenas a carta de observação.}
}
$$
