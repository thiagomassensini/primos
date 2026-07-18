# Mapa das fontes de pesquisa

As fontes abaixo orientaram o bootstrap, mas nenhuma declaracao delas foi
importada automaticamente como teorema Lean.

| Fonte | Papel |
|---|---|
| `GENUINE_C2_CP_RESUMO(1).md` | definicoes Genuine C2/Cp e cancelamento de pernas |
| `CANON_DECOMPOSICAO_ANGULAR_CAMERAS_PRIMAS(2).md` | genealogia, atlas multibase, status e ponte aberta |
| `C2_EQUACAO_ANGULAR_PROJETIVA_MULTIBASE.md` | espaco ponderado, sintese de Riesz e projecao |
| `TEOREMA_CARTA_BRACKETADA_ADAPTADA_A_CARACTERES_DE_DIRICHLET(2).md` | reserva de pesquisa para cartas sincronizadas |
| `Texto colado(76).txt` | implementacao numerica intervalar finita |

Correspondencia atualmente formalizada a partir do resumo Genuine:

| Formula da fonte | Endpoint Lean |
|---|---|
| `F_Cp = D_p - B_p` no nivel de cancelamento finito | `Genuine.finiteCancellation` |
| bracket C2 deixa `2 f(c)` | `Genuine.C2.local_genuine_cancellation` |
| bracket Cp deixa `(p-1) f(c)` | `Genuine.Cp.local_genuine_cancellation` |
| `k_eff(n)=max(v_2(n-1),v_2(n+1))` | `Carry.C2.effectiveDepth` |
| peso efetivo e peso do centro escolhido | `Carry.C2.effectiveDepth_eq_centerDepth` |

Observacao: `GEOMETRIA_C2_CP_DECOMPOSICAO_POR_CARRY(1).md` chegou vazio na
copia de trabalho desta versao e, portanto, nao foi usado para afirmacoes.
