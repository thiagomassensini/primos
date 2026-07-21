# Checkpoint 0.53 — operador espectral real Genuine-first

## Amplitude crítica, órbita unitária, câmeras primas e certificado canônico de grade

**Diretriz:** `GENUINE_FIRST`  
**Objeto formal:** fatia espectral real da geometria já verificada em Lean 4  
**Objeto computacional:** auditoria finita por corte `M` e grade decimal indexada  
**Regra canônica:** nenhum refinamento contínuo altera um ponto publicado

---

## 0. Veredito

A construção proposta não introduz uma função alheia ao Genuine e não precisa
começar por uma varredura bidimensional do plano complexo. Ela toma como dado
geométrico o equilíbrio quadrático do carry, fixa a amplitude crítica e deixa
somente a rotação real como parâmetro livre:

\[
\boxed{\psi_t(n)=n^{-1/2}e^{-it\log n},\qquad t\in\mathbb R.}
\]

O corpo de estados continua sendo complexo porque uma amplitude com fase vive
naturalmente em um plano real de duas dimensões. Entretanto, o **espaço de
parâmetros espectrais é real**. A variável `t` não é obtida depois como a parte
imaginária de uma busca livre em `s`; ela parametriza a órbita unitária gerada
pelas frequências aritméticas `log n` depois que a geometria de carry já fixou
a amplitude `n^(-1/2)`.

No código e no Lean, esta órbita é exatamente a restrição

\[
s(t)=\frac12+it
\]

do campo de Dirichlet já construído. A igualdade é uma **identificação de
representações**, não uma mudança de genealogia: carry, unit-mass, bracket,
TFVD e Green vêm antes; a notação complexa é a ferramenta que codifica a
rotação.

O resultado computacional canônico também é real e finito:

\[
\boxed{t_k=t_{\min}+k\,\Delta t,\qquad k\in\mathbb N.}
\]

Sem refinamento, cada ressonância publicada é literalmente o par

```text
(grid_index = k, exact_decimal_t = t_min + k*dt)
```

selecionado pelo corte, pela grade, pelas câmeras e pela regra de mínimo local.
A avaliação do score ainda usa funções transcendentes em `float64`; portanto o
**ponto de grade é exato como dado finito**, enquanto o valor do score é uma
auditoria numérica reprodutível, não aritmética exata nem prova intervalar do
zero contínuo.

---

## 1. O que vem da geometria do carry

O arquivo de referência `LINHA_CRITICA.md` separa as duas coordenadas que antes
eram empacotadas em `s = sigma + it`:

\[
\boxed{\sigma\text{ calibra a energia};\qquad t\text{ escolhe o alinhamento angular}.}
\]

A massa de uma camada de carry de profundidade `k` na câmera `p` é `p^(-k)`.
Em Hilbert, a amplitude correspondente é sua raiz quadrada:

\[
\sqrt{p^{-k}}=p^{-k/2}.
\]

Logo a coordenada radial deixa de ser uma liberdade espectral do novo
operador. Ela é determinada pela própria passagem de massa para amplitude:

\[
|p^{-k(1/2+it)}|^2=p^{-k}.
\]

O parâmetro restante gira a camada:

\[
p^{-k(1/2+it)}=p^{-k/2}e^{-ikt\log p}.
\]

Pela fatoração única,

\[
e^{-it\log n}=\prod_p e^{-itv_p(n)\log p}.
\]

Assim, `t` aciona simultaneamente as rodas de fase de todas as câmeras primas,
mas não altera sua massa.

### Estatuto no Lean

A formalização vigente já contém, entre outros:

- `criticalLineParameter : ℝ → ℂ`, com parte real `1/2` e parte imaginária `t`;
- a invariância desta fatia pela reflexão `s ↦ 1-conj(s)`;
- a norma exata dos valores positivos de Dirichlet;
- a saturação do operador de ramo e a rigidez do tilt em `1/2`;
- a positividade Green refletida em todo o strip;
- a distinção formal entre zero da síntese e nulidade do vetor coordenado.

O módulo novo `CpRealSpectralOperator.lean` apenas **nomeia e compõe** essa fatia
real. Ele não pressupõe um zero, não usa uma tabela de alturas e não redefine o
Genuine.

---

## 2. Estado espectral real

Indexando os vértices positivos a partir de zero, o estado é

\[
\psi_t(n+1)=(n+1)^{-1/2}e^{-it\log(n+1)}.
\]

No Lean:

```lean
def realSpectralState (t : ℝ) (n : ℕ) : ℂ :=
  positiveDirichletValue (criticalLineParameter t) n
```

O kernel verifica a amplitude:

\[
\boxed{\|\psi_t(n+1)\|=(n+1)^{-1/2}.}
\]

Portanto `t` altera somente a direção do vetor no plano de fase. O quadrado da
amplitude é a massa crítica `1/(n+1)`.

Uma leitura operatorial natural é introduzir, na base dos vértices, o gerador
real diagonal

\[
L|n\rangle=(\log n)|n\rangle,
\]

com órbita unitária

\[
U_t=e^{-itL},\qquad U_t|n\rangle=e^{-it\log n}|n\rangle.
\]

O presente checkpoint formaliza a órbita e suas câmeras. A promoção de cada
ressonância a autovalor de um operador fechado específico exigirá nomear esse
operador e provar seu domínio, auto-adjunticidade ou relação espectral
correspondente. Até lá, o termo rigoroso é **ressonância espectral real da
síntese finita**.

---

## 3. Bracket como curvatura interior

Para centro `c` e raio `j`, defina

\[
\mathcal B_{c,j}[\psi_t]=\psi_t(c-j)-2\psi_t(c)+\psi_t(c+j).
\]

Este é o mesmo `centeredSecondDifference` já usado na formalização C2/Cp. Para
uma câmera prima ímpar, com

\[
h_p=\frac{p-1}{2},
\]

o corte finito é

\[
\boxed{
S_{p,M}(t)
=\sum_{n=1}^{h_p}\psi_t(n)
 +\sum_{m=1}^{M}\sum_{j=1}^{h_p}\mathcal B_{pm,j}[\psi_t].
}
\]

No Lean, isso é literalmente

```lean
finiteBracketedDirichletChart p M (criticalLineParameter t)
```

e o kernel já prova que, para `p` primo ímpar, esse objeto coincide em cada
corte com a carta finita Genuine construída combinatoriamente:

```lean
finiteBracketedDirichletChart_eq_finiteChart
```

Não existe aproximação nessa identificação finita.

---

## 4. Fator de bordo da câmera

O fator formal da câmera é

\[
F_p(s)=1-p^{1-s}.
\]

Na fatia real crítica,

\[
\begin{aligned}
F_p(t)&=F_p\!\left(\frac12+it\right)\\
&=1-p^{1/2-it}\\
&=\boxed{1-\sqrt p\,e^{-it\log p}}.
\end{aligned}
\]

Esta não é uma calibração ajustada numericamente. É a restrição exata de
`cpChartFactor`:

```lean
def realSpectralChartFactor (p : ℕ) (t : ℝ) : ℂ :=
  cpChartFactor p (criticalLineParameter t)
```

Como `Re(s(t))=1/2<1`, o kernel prova que o fator nunca zera para todo primo
`p`. A câmera finita normalizada é

\[
\Phi_{p,M}(t)=\frac{S_{p,M}(t)}{F_p(t)}.
\]

A câmera infinita normalizada já formalizada é

\[
\Phi_p(t)=\operatorname{cpGenuineQuotient}\left(p,\frac12+it\right).
\]

Para qualquer primo ímpar, o Lean prova

\[
\boxed{\Phi_p(t)=\mathcal G\!\left(\frac12+it\right),}
\]

onde `G` é `genuineContinuation`. Assim as câmeras não são funções
independentes que coincidem por sorte: são representações locais, provadas
compatíveis, do mesmo canal Genuine.

---

## 5. Operador multibase finito

Para um conjunto finito de câmeras `K`, o observável escalar do script é

\[
\boxed{\widehat{\mathcal M}_{K,M}(t)=\frac1{|K|}\sum_{p\in K}\Phi_{p,M}(t).}
\]

Antes da síntese, cada semente e cada bracket permanece uma coordenada. Se
`z_e(t)` denota todas essas coordenadas já normalizadas pelo fator da câmera e
por `|K|`, então

\[
\widehat{\mathcal M}_{K,M}(t)=\sum_e z_e(t).
\]

O score usado no programa é

\[
\boxed{
\mathscr A_{K,M}(t)
=\frac{|\sum_e z_e(t)|^2}{N_{K,M}\sum_e|z_e(t)|^2}.
}
\]

Se

\[
e_{K,M}=\frac1{\sqrt{N_{K,M}}}(1,\ldots,1),
\]

temos

\[
\mathscr A_{K,M}(t)
=\frac{|\langle e_{K,M},z(t)\rangle|^2}{\|z(t)\|^2}
=\cos^2\Theta_{K,M}(t).
\]

Portanto

\[
0\le\mathscr A_{K,M}(t)\le1.
\]

Um score pequeno significa que uma corrente coordenada ativa está quase no
hiperplano cego da síntese. Não significa que cada bracket seja pequeno e não
significa destruição de energia.

Essa leitura é compatível com os ledgers Lean da síntese escalar: o setor
invisível é preservado por `finitePortSynthesisKernelValue`, possui soma zero e
reconstrói exatamente a diferença entre parear antes e depois da compressão.

---

## 6. A válvula discreta e o ledger de energia

Para uma sequência finita `f`, o bracket completo é

\[
(\mathcal Bf)_n=f_{n+2}-2f_{n+1}+f_n.
\]

O traço conserva os dois modos apagados pela segunda diferença:

\[
\operatorname{Tr}f=(f_0,f_1-f_0).
\]

O retorno afim e o Green triangular satisfazem

\[
\boxed{I=\mathcal G\mathcal B+\mathsf R\operatorname{Tr}.}
\]

A auditoria fornecida, no estado real-espectral e em `N=15`, encontrou erro de
reconstrução da ordem de `10^-14`. O valor mais importante, porém, é o ledger
polarizado:

\[
\boxed{
\|f\|^2
=\|\mathcal G\mathcal Bf\|^2
 +\|\mathsf R\operatorname{Tr}f\|^2
 +2\operatorname{Re}\langle\mathcal G\mathcal Bf,
          \mathsf R\operatorname{Tr}f\rangle.
}
\]

Na execução reauditada para `t=14.13472514173469`:

```text
||f||²                         =       3.318228993229
||G Bf||²                      =    2536.939527...
||R Tr f||²                    =    2526.207275...
2 Re <G Bf, R Tr f>            =   -5059.828572...
ledger reconstruído            =       3.318228993229
```

Interior e bordo são grandes, mas o termo cruzado é igualmente estrutural. É
esse cancelamento polarizado que impede a leitura incorreta de “energia
criada” ou “energia perdida”.

---

## 7. Protocolo canônico sem refinamento

### 7.1 Definição da grade

A grade não deve ser construída por somas sucessivas em ponto flutuante. O
programa canônico usa índices inteiros e aritmética decimal para o dado
publicado:

\[
\boxed{t_k=t_{\min}+k\,\Delta t.}
\]

O `float64` correspondente é criado apenas para avaliar `log`, `exp` e o
score. Isso remove saídas artificiais como

```text
14.13469999999855
```

do certificado e as substitui pelo ponto de grade que realmente foi pedido:

```text
k = 131347
exact_decimal_t = 14.1347
```

### 7.2 Seleção

1. Calcular o score em todos os pontos da grade.
2. Detectar vales de `-log10(score)` com a proeminência declarada.
3. Reavaliar cada candidato e seus dois vizinhos em CPU/NumPy `float64`.
4. Publicar somente o índice cujo score não excede nenhum vizinho.
5. Aplicar o threshold declarado.
6. Não mover o ponto publicado.

GPU pode acelerar a descoberta. A decisão publicada é reavaliada em CPU.

### 7.3 Estatuto de exatidão

O protocolo sem refinamento fornece:

- **exato:** `k`, `t_min`, `dt`, `t_k`, câmeras, `M` e regra de seleção;
- **determinístico no ambiente fixado:** o score `float64` e seus vizinhos;
- **não afirmado:** que `t_k` seja o zero exato de uma função contínua;
- **não afirmado:** que um corte finito já seja o operador completado;
- **não necessário para o certificado de grade:** `minimize_scalar` ou outro
  refinamento local.

O refinamento permanece disponível somente como diagnóstico opt-in e é salvo
num campo separado, nunca substituindo o certificado canônico.

---

## 8. Auditoria empírica recebida

Foram fornecidas onze execuções sem refinamento, todas com as câmeras

```text
K = (3, 5, 7, 11)
```

e threshold `10^-6`. Em todas as execuções no intervalo `1 ≤ t ≤ 50`, o scan
detectou onze vales brutos e reteve dez.

### 8.1 Reprodutibilidade literal

As repetições

```text
M=512, dt=0.0001
M=256, dt=0.0001
```

produziram listas e scores idênticos nas execuções registradas. Isso é uma
evidência direta de determinismo do pipeline utilizado.

### 8.2 Melhor grade reportada

Para

```text
M  = 1024
dt = 0.000005
```

os pontos canônicos são:

| # | índice `k` | `t_k` decimal exato | score reportado |
|---:|---:|---:|---:|
| 1 | 2,626,947 | 14.134735 | 3.869829e-14 |
| 2 | 4,004,406 | 21.022030 | 1.204280e-13 |
| 3 | 4,802,173 | 25.010865 | 1.382647e-13 |
| 4 | 5,884,980 | 30.424900 | 1.712642e-15 |
| 5 | 6,387,017 | 32.935085 | 5.969820e-14 |
| 6 | 7,317,239 | 37.586195 | 6.420778e-14 |
| 7 | 7,983,739 | 40.918695 | 1.265025e-13 |
| 8 | 8,465,411 | 43.327055 | 1.775429e-13 |
| 9 | 9,401,027 | 48.005135 | 5.248456e-13 |
| 10 | 9,754,758 | 49.773790 | 9.552376e-15 |

Os índices acima usam `t_min=1` e a lei `t_k=1+k·0.000005`.

### 8.3 Dependência do corte

A estabilidade melhora ao aumentar `M`, mas os pontos ainda se deslocam com o
corte. Entre as execuções `M=512, dt=0.00005` e
`M=1024, dt=0.000005`, a média do deslocamento absoluto dos dez vales é
`6.55e-5`. Isso mostra por que o certificado deve sempre carregar `M`: a grade
pode ser muito fina e ainda assim o erro dominante ser a cauda do corte.

O aprofundamento também reduz fortemente os scores. Por exemplo, vários vales
passam da escala `10^-10` em `M=128` para `10^-13` ou menor em `M=1024`.
Essa tendência é consistente com fechamento da carta, mas por si só não prova
a taxa assintótica nem a inexistência de vales adicionais.

---

## 9. O que está provado e o que está auditado

### KERNEL-CHECKED

- a parametrização real `t ↦ 1/2+it`;
- a amplitude crítica dos valores de Dirichlet;
- a segunda diferença/bracket e sua coincidência com o bracket Genuine;
- a identidade da carta finita em todo corte;
- a convergência absoluta das cartas bracketadas para `Re(s)>-1`;
- a não anulação do fator da câmera na fatia crítica;
- a compatibilidade exata entre todas as câmeras primas ímpares;
- a identificação de cada câmera infinita com `genuineContinuation`;
- os ledgers finitos de TFVD, Green, proveniência e síntese escalar;
- a separação entre neutralidade radial e cancelamento angular.

### FINITE_NUMERICAL_GRID_AUDIT

- os vales e scores listados para os cortes e grades recebidos;
- a repetibilidade das execuções duplicadas;
- o fechamento numérico da válvula em precisão de máquina;
- o ledger polarizado de energia no exemplo finito.

### AINDA NÃO PROMOVIDO POR ESTE CHECKPOINT

- um teorema dizendo que cada mínimo finito é um zero contínuo exato;
- um enclosure intervalar em torno de cada ressonância;
- uma prova de convergência das posições dos mínimos quando `M→∞`;
- a definição e auto-adjunticidade do operador fechado do qual todos os `t_n`
  seriam autovalores no sentido funcional-analítico estrito;
- uma nova prova da localização dos zeros a partir apenas do scan, pois a
  coordenada radial já foi fixada pela geometria antes dele.

O último item não enfraquece a rota. Ele explicita sua ordem lógica:

\[
\boxed{\text{carry fixa a amplitude crítica}\longrightarrow
\text{o operador real procura somente as ressonâncias angulares}.}
\]

---

## 10. Arquivos

```text
CPFormal/Analytic/CpRealSpectralOperator.lean
experiments/c2_real_spectral_grid.py
experiments/c2_discrete_valve_boundary.py
experiments/test_c2_real_spectral_grid.py
experiments/results/c2_real_spectral_no_refine_2026-07-21.txt
experiments/results/c2_real_spectral_no_refine_runs.json
docs/REAL_SPECTRAL_OPERATOR.md
```

### Execução canônica

```bash
python3 experiments/c2_real_spectral_grid.py \
  --t-min 1 \
  --t-max 50 \
  --m-cut 1024 \
  --dt 0.000005 \
  --threshold 1e-6 \
  --no-refine \
  --json-output real_spectral_M1024_dt5e-6.json
```

### Testes rápidos

```bash
python3 -m unittest -v experiments/test_c2_real_spectral_grid.py
python3 experiments/c2_discrete_valve_boundary.py
```

---

## 11. Síntese final

A reconstrução Genuine-first correta é:

\[
\boxed{
\text{carry}
\to \text{massa}
\to \text{amplitude }n^{-1/2}
\to \text{órbita real }U_t
\to \text{bracket}
\to \text{câmeras calibradas}
\to \text{síntese multibase}
\to \text{ressonâncias de grade}.
}
\]

A análise complexa não é removida da matemática. Ela deixa de ser a origem da
geometria e volta ao papel natural de linguagem para amplitudes, rotações,
holomorfia e comparação posterior. O novo objeto espectral nasce da estrutura
de carry e vive sobre `t ∈ ℝ`; o plano complexo é o espaço de estados e uma
ferramenta de prova, não o espaço no qual a coordenada radial precisa ser
redescoberta.
