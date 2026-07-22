# Operador empírico Genuine em matrizes reais de rotação

## Resultado

`experiments/c2_real_rotation_operator.py` implementa o scanner espectral,
o mecanismo de câmeras e o ledger Green–bordo–retorno no mesmo programa. O
estado nunca é armazenado como número complexo. Cada coordenada vive em
`R^2`:

\[
\psi_t(n)=\frac1{\sqrt n}R(-t\log n)e_1,
\qquad
R(\theta)=
\begin{pmatrix}
\cos\theta&-\sin\theta\\
\sin\theta&\cos\theta
\end{pmatrix}.
\]

A amplitude `1/sqrt(n)` já está fixada pelo equilíbrio quadrático. O único
parâmetro do movimento é o tempo real `t`.

Em cada câmera prima ímpar `p`, o coração local é o bracket centrado:

\[
\psi_t(pm-r)-2\psi_t(pm)+\psi_t(pm+r),
\qquad
1\le r\le\frac{p-1}{2}.
\]

A calibração da câmera também é real:

\[
C_p(t)=I-\sqrt p\,R(-t\log p),
\qquad
C_p(t)^{-1}
=
\frac1{u^2+v^2}
\begin{pmatrix}u&v\\-v&u\end{pmatrix},
\]

com

\[
u=1-\sqrt p\cos(t\log p),
\qquad
v=\sqrt p\sin(t\log p).
\]

O kernel acelerado calcula diretamente `R(theta)e1`, isto é, a primeira
coluna da matriz. Isso evita guardar milhões de matrizes `2 x 2`, mas é a
mesma operação real. Os testes conferem a igualdade entre a matriz explícita
e essa contração.

## Execução canônica

```bash
python3 experiments/c2_real_rotation_operator.py \
  --tmin 1 \
  --tmax 50 \
  --cutoff 1024 \
  --grid 0.000005 \
  --threshold 1e-6 \
  --no-refine \
  --cameras 3,5,7,11 \
  --backend auto \
  --output results/real_rotation_M1024.json
```

Os aliases antigos continuam aceitos:

| Forma direta | Alias compatível |
|---|---|
| `--tmin` | `--t-min` |
| `--tmax` | `--t-max` |
| `--grid` | `--dt` |
| `--cutoff` | `--m-cut` |
| `--cameras` | `--primes` |
| `--output` | `--json-output` |

Não existe argumento `sigma`, `s` ou número complexo.

## Seleção das câmeras

Uma câmera:

```bash
python3 experiments/c2_real_rotation_operator.py \
  --camera-prime 3 \
  --tmin 10 --tmax 50 --cutoff 512 --grid 0.00005 \
  --threshold 1e-6 --no-refine
```

Um atlas escolhido:

```bash
python3 experiments/c2_real_rotation_operator.py \
  --cameras 3,5,7 \
  --tmin 10 --tmax 50 --cutoff 512 --grid 0.00005 \
  --threshold 1e-6 --no-refine
```

`--camera-prime` pode ser repetido:

```bash
--camera-prime 3 --camera-prime 5 --camera-prime 7
```

## CPU paralela e CuPy

```bash
# CPU, número explícito de processos
--backend cpu --workers 8

# CuPy/CUDA obrigatório; falha claramente se não estiver disponível
--backend cuda --gpu-batch 8192

# Escolha automática: GPU em cargas grandes, CPU paralela no restante
--backend auto
```

Na GPU, os lotes diminuem automaticamente em caso de falta de memória. A
descoberta pode ser feita em CuPy, mas cada candidato publicado é reavaliado
em CPU/NumPy `float64` junto de seus dois vizinhos.

## Balanço de energia e mecanismo

O score continua sendo

\[
\operatorname{score}(t)
=
\frac{\left\|\sum_e z_e(t)\right\|^2}
{N\sum_e\|z_e(t)\|^2}.
\]

Ele mede visibilidade, não desaparecimento da energia coordenada. Para abrir o
mecanismo nos candidatos encontrados:

```bash
--show energy,cameras
```

O relatório separa:

- resultante visível em `R^2`;
- energia total, visível e cega;
- residual sem o fator artificial da dimensão;
- resultantes de semente e bracket;
- cosseno e razão de magnitudes entre os dois canais;
- energia, visibilidade e resultante de cada câmera prima;
- defeitos numéricos da projeção e das matrizes de calibração.

Uma altura real específica também pode ser aberta sem depender do scan:

```bash
--inspect-t 14.1347 --show energy,cameras
```

## Green, bordo e retorno

O mesmo script audita a identidade finita

\[
\boxed{f=G(Bf)+R(\operatorname{Tr}f)}.
\]

Use:

```bash
--show green,boundary,return --ledger-size 15
```

ou simplesmente:

```bash
--show all
```

Os canais significam:

| Canal | Conteúdo |
|---|---|
| `green` | bracket, reconstrução triangular `G(Bf)` e energia interior |
| `boundary` | traço afim `R(Tr f)`, curvatura nula e endpoint |
| `return` | reconstrução completa e ledger polarizado |

O ledger correto é

\[
\|f\|^2
=\|G(Bf)\|^2
+\|R(\operatorname{Tr}f)\|^2
+2\langle G(Bf),R(\operatorname{Tr}f)\rangle_{\mathbb R^2}.
\]

O termo cruzado é preservado. Green e bordo podem carregar energias grandes e
opostas sem que isso seja contado como criação ou perda de energia.

## Grade e refinamento

A coordenada publicada é sempre

\[
t_k=t_{\min}+k\,\Delta t,
\]

construída por índice inteiro e aritmética decimal. `--no-refine` é o padrão
canônico. `--refine` existe apenas como diagnóstico opt-in e sua saída fica em
`refined_noncanonical`; ela nunca substitui o ponto certificado da grade.

## Compatibilidade numérica

O checkpoint

```text
t       = 14.1347
cutoff  = 1024
cameras = 3,5,7,11
```

reproduz os valores do scanner anterior:

```text
coordinate_count = 11275
total_energy     = 0.16447463045995198
score            = 4.98224443013724e-13
```

Essa igualdade é coberta por teste, assim como a equivalência ponto a ponto
entre a formulação escalar antiga e as matrizes reais.

## Testes

```bash
python3 -m unittest -v experiments/test_c2_real_rotation_operator.py
```

Os testes verificam:

- ortogonalidade e determinante das rotações;
- contração acelerada igual à matriz explícita;
- norma `1/n` do estado;
- inversão das câmeras primas;
- igualdade do score com a implementação anterior;
- checkpoint `M=1024`;
- identidade Green–bordo–retorno e ledger de energia;
- ausência de constantes, tipos ou chamadas complexas no código do operador;
- CLI, aliases, seleção de câmera e JSON de saída.

