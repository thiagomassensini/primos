# Adimensionalização dos LSB em Bases Primas

## Estado percentual, energia coletiva e defeito universal de carry

## 1. Motivação

Para um inteiro \(n\) e uma base prima \(p\), o dígito menos significativo é

\[
\operatorname{LSB}_p(n)=n\bmod p.
\]

Os valores brutos, porém, vivem em escalas diferentes:

- na base \(2\): \(0,1\);
- na base \(3\): \(0,1,2\);
- na base \(5\): \(0,1,2,3,4\);
- na base \(p\): \(0,1,\ldots,p-1\).

Somar esses valores diretamente dá mais peso às bases maiores. A ideia central é remover essa unidade artificial e colocar todas as câmeras primas na mesma escala de saturação.

---

## 2. Coordenada adimensional de saturação

Definimos

\[
\boxed{
 x_p(n)=\frac{n\bmod p}{p-1}
}
\]

para cada primo \(p\).

Então

\[
0\leq x_p(n)\leq1.
\]

A interpretação é:

\[
\begin{aligned}
x_p(n)=0 &\quad\Longleftrightarrow\quad \text{câmera vazia ou carry concluído},\\
x_p(n)=1 &\quad\Longleftrightarrow\quad \text{saturação máxima}.
\end{aligned}
\]

Em porcentagem:

\[
100x_p(n)\%.
\]

Exemplos:

| Base | Estados adimensionais |
|---:|---|
| \(2\) | \(0\%,100\%\) |
| \(3\) | \(0\%,50\%,100\%\) |
| \(5\) | \(0\%,25\%,50\%,75\%,100\%\) |
| \(7\) | \(0\%,16{,}67\%,33{,}33\%,50\%,66{,}67\%,83{,}33\%,100\%\) |

Assim, uma unidade deixa de significar “um dígito” e passa a significar “uma fração da capacidade total da câmera”.

---

## 3. Corte natural nas bases primas até \(\sqrt n\)

Um conjunto especialmente natural de câmeras é

\[
\mathcal P_{\sqrt n}=\{p\text{ primo}:p\leq\sqrt n\}.
\]

Esse corte possui uma propriedade aritmética completa:

- se \(n\) é primo, nenhuma câmera em \(\mathcal P_{\sqrt n}\) zera;
- se \(n\) é composto, pelo menos uma câmera em \(\mathcal P_{\sqrt n}\) zera.

Isso acontece porque todo inteiro composto possui ao menos um divisor primo menor ou igual a sua raiz quadrada.

O número de câmeras ativas é

\[
m(n)=\pi(\sqrt n).
\]

---

## 4. Ocupação percentual coletiva

A soma direta das porcentagens pode ultrapassar \(100\%\), pois há várias câmeras. A quantidade coletiva natural é a média:

\[
\boxed{
A(n)=\frac{100}{m(n)}
\sum_{p\leq\sqrt n}
\frac{n\bmod p}{p-1}
}
\]

com

\[
0\%\leq A(n)\leq100\%.
\]

Interpretação:

- \(A(n)\approx0\%\): câmeras coletivamente descarregadas;
- \(A(n)\approx50\%\): equilíbrio médio;
- \(A(n)\approx100\%\): câmeras coletivamente saturadas.

Para uma câmera fixa, ao longo de um ciclo completo, os estados

\[
0,\frac1{p-1},\frac2{p-1},\ldots,1
\]

aparecem igualmente. Portanto,

\[
\boxed{\mathbb E[x_p]=\frac12.}
\]

O fundo universal esperado da ocupação coletiva é, assim,

\[
\boxed{A(n)\approx50\%.}
\]

A adimensionalização remove a tendência de crescimento provocada pelo tamanho das bases.

---

## 5. Energia quadrática

Se \(x_p(n)\) for interpretado como amplitude, a energia média é

\[
\boxed{
E(n)=\frac{100}{m(n)}
\sum_{p\leq\sqrt n}x_p(n)^2
}
\]

A amplitude RMS correspondente é

\[
\boxed{
R(n)=100\sqrt{
\frac1{m(n)}
\sum_{p\leq\sqrt n}x_p(n)^2
}.
}
\]

Para uma câmera fixa,

\[
\mathbb E[x_p^2]
=
\frac{2p-1}{6(p-1)}
=
\frac13+\frac1{6(p-1)}.
\]

Logo, para bases grandes,

\[
\boxed{
\mathbb E[x_p^2]\longrightarrow\frac13.
}
\]

Os valores de fundo são aproximadamente

\[
\boxed{
\begin{aligned}
\text{ocupação média}&\approx50\%,\\
\text{energia média}&\approx33{,}33\%,\\
\text{amplitude RMS}&\approx\frac1{\sqrt3}\approx57{,}735\%.
\end{aligned}
}
\]

---

## 6. Coordenada simétrica de polarização

Para distinguir descarga e saturação em torno de um centro comum, definimos

\[
\boxed{
y_p(n)=2x_p(n)-1.
}
\]

Então

\[
-1\leq y_p(n)\leq1,
\]

com

\[
\begin{aligned}
y_p=-1 &\quad\text{câmera vazia},\\
y_p=0 &\quad\text{meia saturação},\\
y_p=+1 &\quad\text{saturação máxima}.
\end{aligned}
\]

A orientação coletiva é

\[
\boxed{
M(n)=\frac1{m(n)}\sum_{p\leq\sqrt n}y_p(n)
=2\frac{A(n)}{100}-1.
}
\]

A polarização quadrática é

\[
\boxed{
P(n)=\sqrt{
\frac1{m(n)}
\sum_{p\leq\sqrt n}y_p(n)^2
}.
}
\]

Essas duas quantidades medem aspectos diferentes:

- \(M(n)\): direção coletiva, para descarga ou saturação;
- \(P(n)\): distância coletiva do estado intermediário.

Uma configuração com metade das câmeras em \(0\%\) e metade em \(100\%\) pode ter \(M=0\), mas terá polarização alta. Portanto, média e energia não são a mesma informação.

---

## 7. Flips coletivos perfeitos

Com o corte \(p\leq\sqrt n\), existem transições nas quais todas as câmeras passam da saturação máxima para zero:

\[
\boxed{
5\to6,\quad
7\to8,\quad
11\to12,\quad
17\to18,\quad
23\to24,\quad
29\to30.
}
\]

Por exemplo, para \(n=29\), as câmeras ativas são \(2,3,5\):

\[
29\bmod2=1,\qquad
29\bmod3=2,\qquad
29\bmod5=4.
\]

Portanto,

\[
x_2(29)=x_3(29)=x_5(29)=1,
\]

logo

\[
A(29)=100\%,\qquad M(29)=+1.
\]

No inteiro seguinte,

\[
30\bmod2=30\bmod3=30\bmod5=0,
\]

portanto

\[
A(30)=0\%,\qquad M(30)=-1.
\]

O sistema atravessa toda a escala em um único passo.

A transição \(29\to30\) é o último flip global perfeito para esse corte. Depois disso, o primorial dos primos até \(\sqrt n\) cresce mais rapidamente que o próprio \(n\), impedindo que todas as câmeras sejam simultaneamente zeradas ou saturadas.

---

## 8. A dinâmica local de uma câmera

Quando não ocorre carry na base \(p\), o estado aumenta por

\[
\boxed{
 x_p(n)-x_p(n-1)=\frac1{p-1}.
}
\]

Quando \(p\mid n\), a câmera estava saturada em \(n-1\) e cai para zero em \(n\):

\[
\boxed{
 x_p(n)-x_p(n-1)=-1.
}
\]

Assim, na escala adimensional,

\[
\boxed{\text{todo carry é uma queda exata de }100\%.}
\]

Esse valor independe da base. Um carry na base \(2\), \(5\) ou \(1009\) possui a mesma altura adimensional.

---

## 9. Remoção do drift e defeito universal de carry

A subida normal da câmera é \(1/(p-1)\). Retirando esse drift, definimos

\[
\boxed{
 c_p(n)=
\frac{p-1}{p}
\left[
\frac1{p-1}
-
\bigl(x_p(n)-x_p(n-1)\bigr)
\right].
}
\]

A identidade resultante é exata:

\[
\boxed{
 c_p(n)=
\begin{cases}
1,&p\mid n,\\
0,&p\nmid n.
\end{cases}
}
\]

Portanto,

\[
\boxed{c_p(n)=\mathbf1_{p\mid n}.}
\]

Depois da adimensionalização e da retirada da subida de fundo, cada câmera produz um pulso unitário precisamente quando ocorre carry.

O estado percentual pode parecer aproximadamente contínuo, mas o defeito de carry é binário e esparso.

---

## 10. Vetor de carry e energia do defeito

O vetor de carries visíveis é

\[
\boxed{
 c(n)=\bigl(c_p(n)\bigr)_{p\leq\sqrt n}.
}
\]

Sua norma quadrática satisfaz

\[
\|c(n)\|_2^2
=
\sum_{p\leq\sqrt n}c_p(n)^2.
\]

Como cada coordenada vale \(0\) ou \(1\), segue que

\[
\boxed{
\|c(n)\|_2^2
=
\#\{p\leq\sqrt n:p\mid n\}.
}
\]

Ou seja, a energia quadrática é exatamente a quantidade de fatores primos distintos visíveis.

A energia normalizada é

\[
\boxed{
E_{\mathrm{carry}}(n)
=
\frac{\|c(n)\|_2^2}{\pi(\sqrt n)}.
}
\]

A amplitude correspondente é

\[
\boxed{
R_{\mathrm{carry}}(n)
=
\sqrt{
\frac{\#\{p\leq\sqrt n:p\mid n\}}
{\pi(\sqrt n)}
}.
}
\]

Dessa forma,

\[
\boxed{
\begin{aligned}
n\text{ primo}&\Longrightarrow \|c(n)\|_2=0,\\
n\text{ composto}&\Longrightarrow \|c(n)\|_2>0.
\end{aligned}
}
\]

Isso não cria um novo teste de primalidade, pois é equivalente a testar divisibilidade pelos primos até \(\sqrt n\). A contribuição é uma formulação geométrica e energética do mecanismo.

---

## 11. Profundidade de carry

O pulso \(c_p(n)\) detecta apenas se \(p\mid n\). Ele não distingue

\[
p\mid n
\qquad\text{de}\qquad
p^k\mid n.
\]

Para recuperar profundidade, usamos

\[
k_p(n)=v_p(n).
\]

Uma amplitude quadrática natural é

\[
\boxed{
 a_p(n)=
\mathbf1_{p\mid n}\,p^{-v_p(n)/2}.
}
\]

Sua energia é

\[
\boxed{
\|a(n)\|_2^2
=
\sum_{\substack{p\leq\sqrt n\\p\mid n}}
p^{-v_p(n)}.
}
\]

Essa camada distingue:

- muitos carries rasos;
- um carry profundo;
- carries distribuídos em várias bases;
- concentração em uma única base.

Exemplos:

\[
\begin{aligned}
30=2\cdot3\cdot5
&\quad\Rightarrow\quad
\|a(30)\|_2^2=\frac12+\frac13+\frac15,\\
49=7^2
&\quad\Rightarrow\quad
\|a(49)\|_2^2=\frac1{49},\\
48=2^4\cdot3
&\quad\Rightarrow\quad
\|a(48)\|_2^2=\frac1{16}+\frac13.
\end{aligned}
\]

---

## 12. Outros cortes de câmeras

Podemos generalizar o corte para

\[
p\leq n^\theta,
\qquad 0<\theta\leq1.
\]

Para qualquer corte estritamente sublinear \(\theta<1\), as câmeras ativas já completaram muitos ciclos. Por isso, espera-se

\[
A_\theta(n)\approx50\%.
\]

Quando entram todas as bases \(p<n\), aparece uma camada macroscópica de câmeras recém-introduzidas, próximas de seu estado inicial. A média global deixa de ser \(50\%\).

Definindo

\[
A_{\mathrm{all}}(n)
=
\frac1{\pi(n)}
\sum_{p<n}
\frac{n\bmod p}{p-1},
\]

surge assintoticamente

\[
\boxed{
A_{\mathrm{all}}(n)\longrightarrow1-\gamma,
}
\]

onde \(\gamma\) é a constante de Euler–Mascheroni. Numericamente,

\[
1-\gamma\approx0{,}422784335,
\]

ou

\[
\boxed{42{,}2784\%.}
\]

Para a energia média de todas as câmeras,

\[
\boxed{
E_{\mathrm{all}}(n)
\longrightarrow
\log(2\pi)-1-\gamma
\approx0{,}260661401.
}
\]

Logo, a amplitude RMS tende a

\[
\boxed{
\sqrt{\log(2\pi)-1-\gamma}
\approx51{,}0550\%.
}
\]

Isso revela uma mudança de regime:

- cortes sublineares: campo maduro, aproximadamente equilibrado em \(50\%\);
- todas as bases: campo acompanhado por uma fronteira móvel de câmeras recém-nascidas.

---

## 13. Interpretação estrutural

A adimensionalização produz quatro objetos distintos:

### Estado

\[
\boxed{
 x_p(n)=\frac{n\bmod p}{p-1}
}
\]

É a fração de preenchimento da câmera prima.

### Orientação

\[
\boxed{
 y_p(n)=2x_p(n)-1
}
\]

É o lado da câmera em relação à meia saturação.

### Polarização

\[
\boxed{
 P(n)^2=
\frac1{m(n)}
\sum_{p\leq\sqrt n}y_p(n)^2
}
\]

É a energia de afastamento do centro.

### Defeito de carry

\[
\boxed{
 c_p(n)=\mathbf1_{p\mid n}
}
\]

É o evento universal e unitário de reset da câmera.

Essas camadas não devem ser confundidas:

\[
\boxed{
\text{estado percentual}
\neq
\text{energia}
\neq
\text{orientação}
\neq
\text{defeito de carry}.
}
\]

---

## 14. Síntese conceitual

A escala original do LSB depende da base. A escala percentual elimina essa dependência:

\[
\boxed{
\text{bases diferentes possuem capacidades diferentes, mas a mesma geometria de saturação.}
}
\]

Na coordenada adimensional:

1. todas as câmeras vivem em \([0,1]\);
2. a meia saturação universal é \(1/2\);
3. a energia de fundo tende a \(1/3\);
4. a amplitude RMS tende a \(1/\sqrt3\);
5. todo carry é uma queda exata de \(100\%\);
6. removido o drift, o carry vira um pulso binário universal;
7. a norma quadrática do vetor de carries conta os fatores primos distintos visíveis;
8. a profundidade pode ser incorporada com amplitudes \(p^{-v_p(n)/2}\).

A formulação compacta é

\[
\boxed{
\text{estado multibase}
=
\text{ocupação contínua}
+
\text{drift determinístico}
+
\text{defeito esparso de carry}.
}
\]

E a ideia central pode ser resumida por:

\[
\boxed{
\textbf{cada base possui uma escala diferente, mas todo carry possui a mesma altura adimensional: }100\%.
}
\]

---

## 15. Algoritmo experimental mínimo

```python
from math import isqrt, sqrt


def primes_up_to(limit: int) -> list[int]:
    if limit < 2:
        return []

    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"

    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p * p : limit + 1 : p] = b"\x00" * (
                ((limit - p * p) // p) + 1
            )

    return [p for p, is_prime in enumerate(sieve) if is_prime]


def lsb_state(n: int) -> dict[str, object]:
    primes = primes_up_to(isqrt(n))

    if not primes:
        return {
            "n": n,
            "primes": [],
            "occupancy_percent": 0.0,
            "energy_percent": 0.0,
            "rms_percent": 0.0,
            "carry_vector": [],
        }

    x = [(n % p) / (p - 1) for p in primes]
    carry = [1 if n % p == 0 else 0 for p in primes]

    occupancy = sum(x) / len(x)
    energy = sum(value * value for value in x) / len(x)

    return {
        "n": n,
        "primes": primes,
        "coordinates": x,
        "occupancy_percent": 100 * occupancy,
        "energy_percent": 100 * energy,
        "rms_percent": 100 * sqrt(energy),
        "carry_vector": carry,
        "visible_distinct_prime_factors": sum(carry),
        "carry_l2_norm": sqrt(sum(carry)),
    }


for n in [29, 30, 31, 49, 210, 211]:
    print(lsb_state(n))
```

Esse algoritmo calcula simultaneamente:

- as coordenadas percentuais;
- a ocupação coletiva;
- a energia quadrática;
- a amplitude RMS;
- o vetor de carries;
- a quantidade de fatores primos distintos visíveis.

---

## 16. Status matemático das afirmações

### Identidades exatas

- \(x_p(n)=(n\bmod p)/(p-1)\);
- média de uma câmera ao longo do ciclo igual a \(1/2\);
- energia média de uma câmera igual a \((2p-1)/(6(p-1))\);
- carry adimensional como queda de \(100\%\);
- defeito normalizado \(c_p(n)=\mathbf1_{p\mid n}\);
- \(\|c(n)\|_2^2\) igual ao número de fatores primos distintos visíveis.

### Comportamentos assintóticos ou experimentais

- ocupação próxima de \(50\%\) para cortes sublineares;
- energia próxima de \(1/3\);
- amplitude RMS próxima de \(1/\sqrt3\);
- limites globais envolvendo \(1-\gamma\) e \(\log(2\pi)-1-\gamma\);
- diminuição média da ocupação quando aumenta o número de carries simultâneos.

Esses últimos pontos devem ser tratados como resultados assintóticos ou observações numéricas até que sejam formalizados com todas as hipóteses e estimativas de erro necessárias.
