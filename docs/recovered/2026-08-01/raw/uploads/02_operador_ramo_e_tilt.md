# Nota 02 — Operador de ramo e derivação global do tilt

[← Estrutura diádica](01_estrutura_diadica.md) · [Índice](00_indice.md) · [Próxima: Identidade e continuação →](03_identidade_fundamental_e_continuacao.md)

Antes do fechamento fora da linha crítica, isolamos dois mecanismos estruturais
que **detectam** a linha crítica. O operador de ramo produz uma barreira exata
de norma, invariante na direção vertical. O tilt nasce de uma fatoração
algébrica de $n^{-s}$ e produz um bracket de sinal definido fora da linha
crítica. Nenhum dos dois, sozinho, fornece não-anulação global; ambos entram
como insumos dos termos principais e dos orçamentos de erro da Nota 05.

Escrevemos $s=\sigma+it$ com $\sigma>0$.

---

## 2.1. O operador de ramo e sua barreira

Seja
$$
\mathcal{H}_{\mathrm{br}} := \ell^2\bigl(\{-,+\}\times\{2,3,\dots\}\bigr).
$$
O **operador de ramo normalizado** é
$$
\mathcal{W}_s : \mathbb{C}\longrightarrow\mathcal{H}_{\mathrm{br}},
\qquad
(\mathcal{W}_s z)_{\varepsilon,k} := 2^{-ks}\,z.
$$
Os dois valores de $\varepsilon$ representam os dois ramos laterais e o índice
$k\ge 2$ corresponde à primeira profundidade genuína da árvore C2 (Nota 01).

**Proposição 2.1 (norma quadrática do operador de ramo).**
*Para $\sigma>0$,*
$$
\|\mathcal{W}_s\|^2 = 2\sum_{k=2}^{\infty} 2^{-2k\sigma}.
$$
*Em particular, essa norma depende apenas de $\sigma$, não de $t$.*

**Demonstração.**
Para $z\in\mathbb{C}$,
$$
\|\mathcal{W}_s z\|^2
= \sum_{\varepsilon\in\{-,+\}}\sum_{k=2}^{\infty} \bigl|2^{-ks}z\bigr|^2 .
$$
Como $|2^{-ks}|^2 = |2^{-k\sigma}e^{-ikt\log 2}|^2 = 2^{-2k\sigma}$, a fase
vertical desaparece e
$$
\|\mathcal{W}_s z\|^2 = \Bigl(2\sum_{k=2}^{\infty}2^{-2k\sigma}\Bigr)|z|^2. \qquad\blacksquare
$$

Defina a **razão quadrática de ramo**
$$
q_{\mathrm{br}}(\sigma) := 2^{-2\sigma}.
$$

**Teorema 2.2 (fórmula fechada e barreira de ramo).**
*Para $\sigma>0$,*
$$
\|\mathcal{W}_s\|^2 = \frac{2\,q_{\mathrm{br}}(\sigma)^2}{1-q_{\mathrm{br}}(\sigma)},
$$
*e, além disso,*
$$
\|\mathcal{W}_s\|^2 < 1 \Longleftrightarrow \sigma>\tfrac12,
\qquad
\|\mathcal{W}_s\|^2 = 1 \Longleftrightarrow \sigma=\tfrac12,
\qquad
\|\mathcal{W}_s\|^2 > 1 \Longleftrightarrow 0<\sigma<\tfrac12.
$$

**Demonstração.**
Pela Proposição 2.1, basta somar a série geométrica:
$$
2\sum_{k=2}^{\infty} q_{\mathrm{br}}(\sigma)^k
= \frac{2\,q_{\mathrm{br}}(\sigma)^2}{1-q_{\mathrm{br}}(\sigma)}.
$$
Como $0<q_{\mathrm{br}}(\sigma)<1$, a comparação com $1$ é determinada pelo sinal
de
$$
2q_{\mathrm{br}}(\sigma)^2 + q_{\mathrm{br}}(\sigma) - 1
= \bigl(2q_{\mathrm{br}}(\sigma)-1\bigr)\bigl(q_{\mathrm{br}}(\sigma)+1\bigr).
$$
O segundo fator é positivo, e $q_{\mathrm{br}}(\sigma)=\tfrac12$ se, e somente se,
$\sigma=\tfrac12$. Como $q_{\mathrm{br}}$ é estritamente decrescente, obtemos os
três regimes. $\blacksquare$

**Observação 2.3.**
A barreira é uniforme em toda reta vertical. A forma oscilatória fina do ramo
depende de $t$, mas a norma quadrática não: o módulo elimina a fase
$e^{-ikt\log 2}$. Na linha crítica a massa de ramo satura exatamente em $1$.

---

## 2.2. Derivação algébrica do tilt

Defina o **deslocamento transversal**
$$
\delta := \sigma - \tfrac12.
$$
Para todo inteiro positivo $n$, a fatoração
$$
n^{-s} = n^{-1/2}\, n^{-it}\, n^{-\delta}
\tag{2.1}
$$
é exata. Os três fatores separam, respectivamente, a amplitude crítica, a fase
vertical e o deslocamento horizontal.

**Definição 2.4 (tilt global C2).**
Para $\delta\in\mathbb{R}$ e $x>0$, $\operatorname{Tilt}_\delta(x) := x^{-\delta}$.

Se $c = 2^k m$, com $k\ge 2$ e $m$ ímpar positivo, seu **bracket transversal** é
$$
\Theta_\delta(c) := (c-1)^{-\delta} + (c+1)^{-\delta} - 2c^{-\delta}.
\tag{2.2}
$$

**Teorema 2.5 (aniquilação e sinal do tilt).**
*Se $c>1$ e $\delta>-1$, então $\Theta_\delta(c)=0 \iff \delta=0$. Mais
precisamente,*
$$
\delta>0 \Rightarrow \Theta_\delta(c)>0,
\qquad
\delta=0 \Rightarrow \Theta_\delta(c)=0,
\qquad
-1<\delta<0 \Rightarrow \Theta_\delta(c)<0.
$$

**Demonstração.**
Para $f_\delta(x)=x^{-\delta}$,
$$
f_\delta''(x) = \delta(\delta+1)\,x^{-\delta-2}.
$$
Se $\delta>0$, a função é estritamente convexa em $(0,\infty)$, e sua diferença
segunda centrada $\Theta_\delta(c)$ é positiva. Se $-1<\delta<0$, ela é
estritamente côncava, e a diferença é negativa. Para $\delta=0$,
$f_0\equiv 1$, logo $\Theta_0(c)=1+1-2=0$. Os sinais estritos fornecem a
equivalência. $\blacksquare$

**Corolário 2.6 (o tilt detecta a linha crítica).**
*Se $\sigma>0$ e $c>1$, então $\Theta_{\sigma-1/2}(c)=0 \iff \sigma=\tfrac12$.*

**Demonstração.**
Como $\sigma>0$, temos $\sigma-\tfrac12 > -1$; aplique o Teorema 2.5. $\blacksquare$

---

## 2.3. Tilt global e correção de cutoff

Antecipando a notação da Nota 03, seja $\omega_X(n)$ um cutoff e defina
$g_X(n):=\omega_X(n)-1$. Para $c=2^k m$, considere a soma direta regularizada
$$
D_X(s) := \sum_{\substack{k\ge 2\\ m\ge 1,\ m\ \mathrm{ímpar}}}
2^{-k}\bigl(\omega_X(c-1)(c-1)^{-s} + \omega_X(c+1)(c+1)^{-s}\bigr).
$$

**Proposição 2.7 (decomposição exata tilt–cutoff).**
*Em qualquer truncamento finito, e onde as séries convergem absolutamente,*
$$
D_X(s) - B_\infty(s)
= 2\sum_{\substack{k\ge 2\\ m\ge 1,\ m\ \mathrm{ímpar}}} 2^{-k}c^{-s} + R_X(s),
$$
*onde*
$$
R_X(s) := \sum_{\substack{k\ge 2\\ m\ge 1,\ m\ \mathrm{ímpar}}}
2^{-k}\bigl(g_X(c-1)(c-1)^{-s} + g_X(c+1)(c+1)^{-s}\bigr).
$$

**Demonstração.**
Subtraia, em cada centro $c$, o bracket $(c-1)^{-s}+(c+1)^{-s}-2c^{-s}$ da
contribuição regularizada das duas pernas. Usando $\omega_X = 1 + g_X$, as
partes sem cutoff cancelam e restam o centro resgatado $2c^{-s}$ e as duas
correções $g_X(c\pm 1)(c\pm 1)^{-s}$. $\blacksquare$

Aplicando a fatoração (2.1) a cada termo, o tilt $n^{-\delta}$ aparece tanto no
centro quanto no residual de cutoff. Como, para cada $n$ fixo,
$$
\left.\frac{d}{d\delta} n^{-\delta}\right|_{\delta=0} = -\log n,
$$
a primeira variação transversal em torno da linha crítica é uma soma
log-ponderada. Esse é o mecanismo de amplificação que alimenta as cotas de tilt
da Nota 05.

---

## 2.4. A mesma transição em duas linguagens

Combinando os resultados anteriores, obtemos a tricotomia, válida para todo
centro $c>1$:

| Regime | $\|\mathcal{W}_s\|^2$ | $\Theta_{\sigma-1/2}(c)$ | Leitura |
|--------|-----------------------|--------------------------|---------|
| $\sigma>\tfrac12$ | $<1$ | $>0$ | contração / convexidade |
| $\sigma=\tfrac12$ | $=1$ | $=0$ | saturação / aniquilação |
| $0<\sigma<\tfrac12$ | $>1$ | $<0$ | expansão / concavidade |

O operador de ramo vê a transição como contração, saturação e expansão. O tilt
vê a mesma transição como convexidade, aniquilação e concavidade.

**Observação 2.8.**
Esses mecanismos identificam rigidamente a linha crítica, mas não fornecem
sozinhos não-anulação global: a soma global contém fases $n^{-it}$, variação
entre centros e o residual $R_X$. A passagem do sinal local para a não-anulação
global exige as cotas e a dominância estrita da Nota 05.

---

## 2.5. O que esta camada entrega para o middle

A Nota 02 será usada na faixa média de duas formas distintas.

1. O operador de ramo fornece a geometria vertical: a razão real
   $q_{\mathrm{br}}(\sigma)=2^{-2\sigma}$ separa contração, saturação e expansão
   em torno de $\sigma=\tfrac12$. Essa é a leitura estrutural da linha crítica.
2. A fatoração
   $$
   n^{-s}=n^{-1/2}n^{-it}n^{-(\sigma-1/2)}
   $$
   isola o tilt transversal. Quando o operador finito é balanceado no bulk, a
   contribuição de tilt aparece como uma família semeada
   $T_j(s)=A(s)q_{\mathrm v}(s)^j$, cuja soma é controlada por um orçamento do
   tipo
   $$
   T_{\mathrm{up}}(s)
   =
   \frac{C_T(s)}{X_T(s)}\,\frac{1}{1-\|q_{\mathrm v}(s)\|}.
   $$

**Saída da Nota 02.**
O operador de ramo e o tilt não são a prova de não-anulação. Eles entregam a
geometria e um dos resíduos orçamentados na desigualdade de dominância do
quarteto:
$$
V_{\mathrm{debt}}(s)+T_{\mathrm{up}}(s)+H_{\mathrm{up}}(s)+C_{\mathrm{up}}(s)
<\mathfrak Q(s).
$$
Essa desigualdade, e não a barreira isolada, é o mecanismo de fechamento da
Nota 05.

---

[← Estrutura diádica](01_estrutura_diadica.md) · [Índice](00_indice.md) · [Próxima: Identidade e continuação →](03_identidade_fundamental_e_continuacao.md)
