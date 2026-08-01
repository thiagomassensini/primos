# Derivação Algébrica do Tilt C2

> **Escopo.** Esta nota isola somente a derivação do **tilt C2 global** e os mecanismos imediatamente conectados a ele: bracket, sinal, cutoff, termo cruzado, amplificação e as leituras locais de pacote que apareceram nas notas `R2` e `Y2`.
>
> **Resumo em uma frase.** O tilt não é uma heurística: ele nasce da fatoração exata
>
> $$
> n^{-s}=n^{-1/2}\,n^{-it}\,n^{-(\sigma-1/2)}.
> $$
>
> Em $\sigma=1/2$, o fator transversal vira a constante $1$, e o bracket C2 aniquila constantes:
>
> $$
> \Delta^2[1](c)=1+1-2=0.
> $$

---

## 1. Notação mínima

Escrevemos

$$
s=\sigma+it,
\qquad
\delta=\sigma-\frac12.
$$

Então

$$
s=\frac12+\delta+it.
$$

Para cada centro C2

$$
c=2^k m,
\qquad
k\ge2,
\qquad
m\ \text{ímpar},
$$

as duas pernas laterais são

$$
c-1,
\qquad
c+1.
$$

O bracket C2 é a diferença segunda discreta centrada:

$$
\boxed{
\Delta^2[f](c)=f(c-1)+f(c+1)-2f(c).
}
$$

---

## 2. A derivação algébrica do tilt

A partir de

$$
n^{-s}=n^{-(\sigma+it)},
$$

substituímos $\sigma=1/2+\delta$:

$$
n^{-s}=n^{-(1/2+\delta+it)}.
$$

Separando os fatores:

$$
\boxed{
 n^{-s}=n^{-1/2}\,n^{-it}\,n^{-\delta}.
}
$$

Como $\delta=\sigma-1/2$, temos também

$$
\boxed{
 n^{-s}=n^{-1/2}\,n^{-it}\,n^{-(\sigma-1/2)}.
}
$$

Daí nasce o objeto:

$$
\boxed{
\operatorname{Tilt}_\delta(n):=n^{-\delta}=n^{-(\sigma-1/2)}.
}
$$

Essa definição não é uma hipótese. É uma fatoração algébrica exata de $n^{-s}$ em três partes:

| Fator | Expressão | Papel |
|---|---:|---|
| amplitude crítica | $n^{-1/2}$ | fixa a escala da linha crítica |
| fase vertical | $n^{-it}$ | gera oscilação em $t$ |
| tilt transversal | $n^{-\delta}$ | mede deslocamento lateral em $\sigma$ |

---

## 3. O ponto crítico: quando o tilt vira constante

Se

$$
\sigma=\frac12,
$$

então

$$
\delta=\sigma-\frac12=0.
$$

Logo

$$
\operatorname{Tilt}_0(n)=n^0=1.
$$

Portanto, na linha crítica, o tilt é uma função constante.

Aplicando o bracket:

$$
\Delta^2[\operatorname{Tilt}_0](c)
=
\Delta^2[1](c)
=
1+1-2
=0.
$$

Assim:

$$
\boxed{
\sigma=\frac12
\Longrightarrow
\delta=0
\Longrightarrow
\operatorname{Tilt}_\delta(n)=1
\Longrightarrow
\Delta^2[\operatorname{Tilt}_\delta](c)=0.
}
$$

Esta é a identidade-mãe do mecanismo.

---

## 4. Bracket aplicado ao tilt

Para $\delta$ qualquer, o bracket transversal do tilt é

$$
\boxed{
\Delta^2[n^{-\delta}](c)
=
(c-1)^{-\delta}+(c+1)^{-\delta}-2c^{-\delta}.
}
$$

Em $\delta=0$:

$$
(c-1)^0+(c+1)^0-2c^0=1+1-2=0.
$$

Fora de $\delta=0$, o objeto deixa de ser constante. A diferença segunda passa a medir a curvatura discreta do campo transversal $n^{-\delta}$.

Para $c$ grande, a aproximação contínua/Taylor dá

$$
\Delta^2[n^{-\delta}](c)
\approx
\frac{d^2}{dx^2}x^{-\delta}\bigg|_{x=c}
=
\delta(\delta+1)c^{-\delta-2}.
$$

Ou seja: o bracket vê diretamente a curvatura do tilt.

---

## 5. Sinal definido: convexidade e concavidade

Considere

$$
f(x)=x^{-\delta}.
$$

Então

$$
f''(x)=\delta(\delta+1)x^{-\delta-2}.
$$

Na faixa crítica natural $-1<\delta$, temos:

| Regime | Forma de $f(x)=x^{-\delta}$ | Sinal de $\Delta^2[f](c)$ | Leitura |
|---|---|---:|---|
| $\delta>0$ | estritamente convexa | $>0$ | tilt positivo acumula curvatura positiva |
| $\delta=0$ | constante | $=0$ | tilt aniquilado |
| $-1<\delta<0$ | estritamente côncava | $<0$ | tilt negativo acumula curvatura negativa |

Portanto:

$$
\boxed{
\delta>0\Rightarrow \Delta^2[n^{-\delta}](c)>0,
}
$$

$$
\boxed{
\delta=0\Rightarrow \Delta^2[n^{-\delta}](c)=0,
}
$$

$$
\boxed{
-1<\delta<0\Rightarrow \Delta^2[n^{-\delta}](c)<0.
}
$$

O ponto importante é que o sinal é **uniforme por bracket**. Para $\delta\ne0$, todos os brackets têm a mesma orientação de curvatura. Não é ruído de fase. Não é leitura estatística. É convexidade/concavidade.

---

## 6. Forma C2: pernas, centro e cutoff

O operador C2 usa a decomposição por brackets. Sem cutoff, a soma direta das pernas pode ser escrita como

$$
D_{\rm nocut}(s)
=
\sum_{k,m}2^{-k}\left[(c-1)^{-s}+(c+1)^{-s}\right].
$$

O bracket é

$$
B(s)
=
\sum_{k,m}2^{-k}\left[(c-1)^{-s}+(c+1)^{-s}-2c^{-s}\right].
$$

Subtraindo, as pernas cancelam formalmente e sobra o centro:

$$
D_{\rm nocut}(s)-B(s)
=
2\sum_{k,m}2^{-k}c^{-s}.
$$

Com cutoff suave, escrevemos

$$
g_X(n)=e^{-n/X}-1.
$$

Então a forma de soma única é

$$
\boxed{
D_X(s)-B(s)
=
\sum_{k,m}2^{-k}
\left[
(c-1)^{-s}g_X(c-1)
+(c+1)^{-s}g_X(c+1)
+2c^{-s}
\right].
}
$$

Essa forma separa o mecanismo em:

1. **pernas com correção de cutoff**;
2. **centro resgatado**;
3. **tilt transversal escondido em cada $n^{-s}$**.

---

## 7. Por que o cutoff suave importa

O cutoff suave não cria o tilt. O tilt já veio da fatoração de $n^{-s}$.

O papel do cutoff suave é outro:

1. regularizar a soma;
2. preservar a variação lenta entre $c-1$, $c$ e $c+1$;
3. não destruir o cancelamento delicado do bracket.

A observação operacional das rotas K/K3 foi:

| Cutoff | Efeito sobre a seletividade em $\sigma=1/2$ |
|---|---|
| suave, tipo $e^{-n/X}$ | preserva o mecanismo |
| super-suave, tipo $e^{-(n/X)^2}$ | melhora a seletividade |
| polinomial suave | ainda preserva |
| sharp/descontínuo | destrói o cancelamento |
| sem cutoff | perde a seletividade no modelo truncado |

Moral: o cutoff suave é regularizador. O tilt é algébrico.

---

## 8. Decomposição tilt versus cutoff

Nas rotas K3/K4, a decomposição conceitual aparece como

```text
D_k - B_k = [D_k_nocut - B_k] + [D_k - D_k_nocut]
          = tilt_term          + cutoff_term
          = 2·Center_k         - Deficit_k
```

A leitura é:

- `tilt_term`: o componente estrutural ligado ao bracket e ao centro;
- `cutoff_term`: o déficit introduzido por $e^{-n/X}$;
- em $\sigma=1/2$, os dois vetores podem ficar quase opostos, gerando cancelamento muito forte;
- fora de $\sigma=1/2$, o tilt ativo introduz componente de sinal definido.

No nível de mecanismo:

$$
\delta=0
\Rightarrow
\text{sem curvatura de tilt}
\Rightarrow
\text{sobra majoritariamente resíduo oscilatório de cutoff}.
$$

$$
\delta\ne0
\Rightarrow
\text{curvatura de tilt com sinal definido}
\Rightarrow
\text{acúmulo coerente}
\Rightarrow
\text{menos cancelamento}.
$$

---

## 9. Termo cruzado: o disjuntor transversal

Expanda o tilt:

$$
n^{-\delta}=e^{-\delta\log n}.
$$

Para $|\delta|$ pequeno:

$$
\boxed{
 n^{-\delta}
 =
 1-\delta\log n+rac{\delta^2\log^2 n}{2}+O(\delta^3\log^3 n).
}
$$

Substituindo em $D-B$:

$$
D-B(\delta)
=
(D-B)|_{\delta=0}
+
\delta\,\partial_\delta(D-B)|_{\delta=0}
+
\frac{\delta^2}{2}\,\partial_\delta^2(D-B)|_{\delta=0}
+
\cdots.
$$

O termo zeroth é o resíduo em $\sigma=1/2$:

$$
(D-B)|_{\delta=0}.
$$

O primeiro termo transversal é log-ponderado:

$$
\partial_\delta(D-B)|_{\delta=0}
\sim
-\sum \log(n)\, (\cdots).
$$

Essa é a razão de ele funcionar como amplificador: sair de $\delta=0$ ativa uma soma com peso $\log n$.

Em linguagem curta:

$$
\boxed{
\text{tilt fora da linha crítica}
\quad\Longrightarrow\quad
\text{termo log-ponderado}
\quad\Longrightarrow\quad
\text{amplificação transversal}.
}
$$

---

## 10. Cadeia lógica compacta

```text
n^{-s}
  = n^{-1/2} · n^{-it} · n^{-(σ-1/2)}
                         │
                         ▼
              Tilt(n) = n^{-δ}, δ = σ - 1/2
                         │
                         ▼
Δ²[Tilt](c) = (c-1)^(-δ) + (c+1)^(-δ) - 2c^(-δ)
                         │
      ┌──────────────────┴──────────────────┐
      ▼                                     ▼
δ = 0                                 δ ≠ 0
Tilt = 1                              Tilt não constante
Δ²[1] = 0                             Δ²[n^{-δ}] tem sinal definido
curvatura zerada                      curvatura coerente
      │                                     │
      ▼                                     ▼
resíduo oscilatório de cutoff          acúmulo coerente do tilt
cancela fortemente                     quebra/tilta o cancelamento
```

---

## 11. Status lógico do tilt

| Afirmação | Status | Motivo |
|---|---|---|
| $n^{-s}=n^{-1/2}n^{-it}n^{-(\sigma-1/2)}$ | algébrico exato | fatoração direta |
| $\operatorname{Tilt}(n)=n^{-\delta}$ | definição derivada | $\delta=\sigma-1/2$ |
| $\Delta^2[1]=0$ | algébrico exato | diferença segunda de constante |
| $\delta>0\Rightarrow\Delta^2[n^{-\delta}]>0$ | analítico elementar | convexidade |
| $-1<\delta<0\Rightarrow\Delta^2[n^{-\delta}]<0$ | analítico elementar | concavidade |
| cutoff suave preserva o mecanismo | estrutural + verificado | regularidade evita erro sharp |
| termo cruzado amplifica deslocamento em $\delta$ | expansão Taylor | aparece peso $\log n$ |
| conclusão global sobre zeros | depende de fechamentos adicionais | convergência, bounds, transferência, controle global |

A parte importante: **o tilt e sua aniquilação em $\sigma=1/2$ não são heurísticos**. O que exige outras provas são as consequências globais que usam esse mecanismo.

---

# Apêndice A — Leitura local de pacote: `W₂` como tilt angular

As notas `pi_rest_R2_*` mostram uma versão local/packet-level do mesmo tema: um deslocamento angular consumindo orçamento de fase.

## A.1. Fatorização do pacote `W₂`

Para o caso local estudado:

$$
J_2(s)=3+W_2(s),
$$

com

$$
W_2(s)
=
2\left(\frac53\right)^{-s}
+2\left(\frac73\right)^{-s}.
$$

Equivalente:

$$
W_2(s)=4\left(\frac{35}{9}\right)^{-s/2}
\cosh\left(\frac{s}{2}\log\frac75\right).
$$

Separando fase:

$$
W_2(s)
=
4\left(\frac{35}{9}\right)^{-\sigma/2}e^{-i\phi}G_2(s),
\qquad
\phi=\frac t2\log\frac{35}{9}.
$$

Aqui aparece um tilt angular local: o carrier $e^{-i\phi}$ gira o pacote em relação ao eixo negativo.

## A.2. Coordenada `q` como orçamento de tilt

Na geometria local, define-se

$$
\phi_{\rm dist}=a u,
\qquad
a=\frac12\log\frac{35}{9}.
$$

Com

$$
\ell_{\rm long}=\frac{\varepsilon}{a-b},
\qquad
q=\frac{u}{\ell_{\rm long}},
\qquad
\Phi_*=a\ell_{\rm long},
$$

segue a identidade exata:

$$
\boxed{
q=\frac{\phi_{\rm dist}}{\Phi_*}.
}
$$

Logo `q` não é só coordenada de janela: é a fração do orçamento angular de tilt do carrier já consumida.

## A.3. Desvio total do pacote

O desvio angular total do pacote é

$$
\delta_W=\phi_{\rm dist}+|\arg G_2|.
$$

Normalizando:

$$
\boxed{
\frac{\delta_W}{\Phi_*}
=
q+\frac{|\arg G_2|}{\Phi_*}.
}
$$

Leitura: o tilt local do pacote é a soma de uma parte geométrica/carrier e uma correção analítica do núcleo.

## A.4. Como `W₂` inclina `J₂`

Como

$$
J_2(s)=3+W_2(s),
$$

temos

$$
\tan |\arg J_2(s)|
=
\frac{|\Im W_2(s)|}{3+\Re W_2(s)}.
$$

Então `J₂` fica muito inclinado quando:

1. $W_2$ empurra forte para a esquerda;
2. $3+\Re W_2$ fica pequeno;
3. $|\Im W_2|$ continua significativo.

Esse é o mecanismo local de tilt por quase-cancelamento real.

## A.5. Fórmula de left-push

O empurrão real do pacote é

$$
\boxed{
-\Re W_2(s)
=
4\left(\frac{35}{9}\right)^{-\sigma/2}|G_2(s)|\cos(\delta_W).
}
$$

Equivalentemente:

$$
\boxed{
3+\Re W_2(s)
=
3-
4\left(\frac{35}{9}\right)^{-\sigma/2}|G_2(s)|\cos(\delta_W).
}
$$

Portanto o cancelamento real local é controlado por:

1. amplitude do pacote;
2. desvio angular do pacote;
3. cosseno desse desvio.

---

# Apêndice B — Tilt de reentrada: cancelamento angular em `-A/A'`

Nas notas `pi_rest_reentry_Y2_*`, aparece uma noção local de tilt no passo linear.

Defina

$$
\alpha=\arg(A)-\frac\pi2,
\qquad
\beta=\arg(A').
$$

Então

$$
\boxed{
\arg\left(-\frac{A}{A'}\right)
=
-\frac\pi2+\alpha-\beta.
}
$$

A distância do passo linear ao eixo vertical descendente é

$$
\boxed{
\delta_{\rm lin}
=
\arg\left(-\frac{A}{A'}\right)+\frac\pi2
=
\alpha-\beta.
}
$$

Leitura:

- se $\alpha\approx\beta$, os tilts se cancelam e o passo aponta quase verticalmente;
- se $\alpha-\beta$ é grande, o passo sai da faixa vertical.

Isso é local, mas conversa com o mesmo princípio: decompor uma fase em partes e identificar qual componente transversal realmente inclina o mecanismo.

---

# Apêndice C — Forcing sheetwise: fase por gap vertical

No curto passo $M\to M+2$, a atualização C2 adiciona um único termo:

$$
A_{M+2}(s)-A_M(s)=2^{-k}m_{\rm core}^{-s}.
$$

Se $z_M$ é raiz antiga de $A_M$, então

$$
A_M(z_M)=0
$$

e o forcing é exatamente

$$
\boxed{
F_M(z_M)=A_{M+2}(z_M)=2^{-k}m_{\rm core}^{-z_M}.
}
$$

Como $2^{-k}$ é real positivo,

$$
\arg F_M(z_M)
=
-\Im(z_M)\log m_{\rm core}
\pmod{2\pi}.
$$

Para duas sheets:

$$
\boxed{
\arg F_{\rm cap}-\arg F_{\rm pos}
=
-\bigl(\Im z_{\rm cap}-\Im z_{\rm pos}\bigr)\log m_{\rm core}
\pmod{2\pi}.
}
$$

Aqui o tilt angular entre sheets é literalmente o gap vertical multiplicado por $\log m_{\rm core}$.

---

# Apêndice D — Lista curta de arquivos-fonte internos

Esta nota consolida material extraído das seguintes notas/saídas internas:

- `rotas_K_K2_K3_estrutura_algebrica_e_mecanismo.md`
- `Texto colado.txt` — saída da Rota K
- `Texto colado (2).txt` — saída da Rota K4
- `pi_rest_R2_q_tilt_budget_bridge.md`
- `pi_rest_R2_q_balance_threshold.md`
- `pi_rest_R2_transition_gap.md`
- `pi_rest_R2_total_budget_strip.md`
- `pi_rest_R2_pair_cancellation.md`
- `pi_rest_R2_W2_left_push.md`
- `pi_rest_reentry_Y2_linear_tilt_cancellation.md`
- `pi_rest_reentry_Y2_forcing_sheet_phase_split.md`
- `pi_rest_reentry_Y2_vs_packet_scalars.md`

---

# Checklist para uso futuro

Quando precisar reencontrar a derivação do tilt C2 global, procure estes marcadores:

```text
n^{-s} = n^{-1/2} · n^{-it} · n^{-(σ-1/2)}
Tilt(n) = n^{-δ}, δ = σ - 1/2
Δ²[Tilt](c) = (c-1)^{-δ} + (c+1)^{-δ} - 2c^{-δ}
σ = 1/2 ⇒ δ = 0 ⇒ Tilt(n)=1 ⇒ Δ²[1]=0
f''(x)=δ(δ+1)x^{-δ-2}
δ>0 convexa, δ<0 côncava, δ=0 constante
n^{-δ}=exp(-δ log n)
```
