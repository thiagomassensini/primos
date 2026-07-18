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
| `Library/Lean/GlobalDecomposition.lean` | antecedente arquitetural C2 para endereco global e existencia unica; nao importado como prova Cp |

Correspondencia atualmente formalizada a partir do resumo Genuine:

| Formula da fonte | Endpoint Lean |
|---|---|
| `F_Cp = D_p - B_p` no nivel de cancelamento finito | `Genuine.finiteCancellation` |
| bracket C2 deixa `2 f(c)` | `Genuine.C2.local_genuine_cancellation` |
| bracket Cp deixa `(p-1) f(c)` | `Genuine.Cp.local_genuine_cancellation` |
| `k_eff(n)=max(v_2(n-1),v_2(n+1))` | `Carry.C2.effectiveDepth` |
| peso efetivo e peso do centro escolhido | `Carry.C2.effectiveDepth_eq_centerDepth` |
| residuos nao nulos correspondem aos offsets balanceados Cp | `Carry.Cp.balancedOffsetEquivNonzeroResidue` |
| camera Cp possui `p-1` pernas | `Carry.Cp.card_balancedOffsets` |
| cada perna Cp nao multipla possui centro e offset balanceado unicos | `Carry.Cp.nonmultipleEquivIncidence`, `Carry.Cp.existsUnique_incidence` |
| somente o offset canonico da carta Cp produz carry | `Carry.Cp.dvd_sub_iff_eq_offset` |
| profundidade efetiva Cp e a profundidade do centro canonico | `Carry.Cp.effectiveDepth_eq_centerDepth` |
| soma ponderada Cp preserva o peso do carry sob a bijecao | `Carry.Cp.weighted_reindex` |
| caixa Cp arbitraria possui bordo assinado `extras - faltantes` | `Carry.Cp.weighted_reindex_with_boundary` |
| cobertura Cp exata elimina o bordo | `Carry.Cp.weighted_reindex_of_exact_cover` |
| centros Cp `p,2p,...,Mp` com todos os offsets balanceados | `Carry.Cp.alignedIncidenceBox` |
| caixa Cp alinhada possui `M(p-1)` incidencias e pernas | `Carry.Cp.card_alignedIncidenceBox`, `Carry.Cp.card_alignedNonmultipleBox` |
| a caixa direta Cp cobre exatamente a caixa bracketada | `Carry.Cp.incidenceImage_alignedNonmultipleBox` |
| caixas Cp alinhadas possuem extras e faltantes vazios | `Carry.Cp.extraIncidences_alignedBox`, `Carry.Cp.missingIncidences_alignedBox` |
| reindexacao ponderada sem bordo na caixa Cp alinhada | `Carry.Cp.weighted_reindex_alignedBox` |

Observacao: `GEOMETRIA_C2_CP_DECOMPOSICAO_POR_CARRY(1).md` chegou vazio na
copia de trabalho desta versao e, portanto, nao foi usado para afirmacoes.
