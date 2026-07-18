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
| `Library/Lean/OperatorNorm.lean` | antecedente C2 da massa dominante e do criterio de saturacao; auditado, mas a formula Cp foi derivada novamente |
| `Library/Lean/Tilt.lean` | antecedentes de anulacao e sinal do tilt de duas pernas; somente a parte estrutural foi reaproveitada nesta etapa |
| `Library/GENUINE_FIRST/cp_branch_tilt_operator.py` | especificacao Cp do ramo puro, energia por perna, profundidade inicial e tilt multirramo |
| `C2_GREEN_HARDY_BOUNDARY_RELATION.md` | registra que continuidade Green nao fornece por si so o traco de fluxo; usado para manter o certificado concreto aberto |

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
| massa critica `p^(-k)` e amplitude `p^(-k/2)` | `Carry.Cp.criticalMass`, `Carry.Cp.criticalAmplitude` |
| quadrado da amplitude e a massa | `Carry.Cp.criticalAmplitude_sq_eq_mass` |
| o peso concreto de carry atravessa a caixa Cp sem bordo | `Carry.Cp.criticalMass_reindex_alignedBox` |
| massa do ramo em `sigma` e razao `p^(-2 sigma)` | `Carry.Cp.branchMassWeight`, `Carry.Cp.branchRatio` |
| norma quadratica definida pela serie de profundidades | `Analytic.Cp.branchNormSq` |
| forma fechada da norma | `Analytic.Cp.branchNormSq_eq_closed` |
| norma quadratica igual a um exatamente em `sigma=1/2` | `Analytic.Cp.branchNormSq_eq_one_iff` |
| defeito da norma e `sigma-1/2` possuem o mesmo zero | `Analytic.Cp.branchDefect_eq_zero_iff_criticalDisplacement_eq_zero` |
| tilt bracketado de todas as pernas Cp | `Analytic.Cp.cpTilt` |
| norma saturada implica tilt nulo | `Analytic.Cp.branchDefect_zero_implies_cpTiltAtSigma_zero` |
| pareamento exato do tilt por `a ↦ -a` | `Analytic.Cp.cpTilt_eq_half_sum_pair` |
| sinal positivo de cada bracket para `delta>0` | `Analytic.Cp.cpPairTilt_pos_of_delta_pos` |
| sinal negativo de cada bracket para `-1<delta<0` | `Analytic.Cp.cpPairTilt_neg_of_neg_one_lt_delta` |
| rigidez canonica do tilt fora da camera | `Analytic.Cp.tiltRigidityAt_of_halfRange_lt_center` |
| zeros do tilt exatamente na meia abscissa | `Analytic.Cp.cpTiltAtSigma_eq_zero_iff_half` |
| equivalencia entre defeito da norma e tilt no centro admissivel | `Analytic.Cp.branchDefect_eq_zero_iff_cpTiltAtSigma_eq_zero_of_admissible_center` |
| bloco completo = pernas + centro | `Genuine.Cp.centerBlock_eq_legSum_add_center` |
| transladar um bloco completo produz seu intervalo inteiro | `Genuine.Cp.centerBlock_eq_sum_Icc` |
| bracket Cp = bloco completo menos `p` centros | `Genuine.Cp.bracket_eq_centerBlock_sub_p_mul_center` |
| carta finita = prefixo por blocos menos correcao vertical | `Genuine.Cp.finiteChart_eq_blockPrefix_sub_p_mul_centerSum` |
| os blocos alinhados ladrilham `1,...,pM+halfRange(p)` | `Genuine.Cp.blockPrefix_eq_positiveIntervalSum` |
| carta finita = prefixo positivo literal menos centros | `Genuine.Cp.finiteChart_eq_positiveIntervalSum_sub_p_mul_centerSum` |
| identidade Green assinada, energia positiva e bordo fechado implicam `delta=0` | `Analytic.Cp.SignedGreenCertificate.criticalDisplacement_eq_zero_of_genuine_zero` |
| certificado Green concreto produz a ponte Genuine--ramo | `Analytic.Cp.SignedGreenCertificate.toGenuineBranchBridge` |
| ponte ainda aberta de zeros Genuine para a norma | `Analytic.Cp.GenuineBranchBridge` (sem instancia) |

Observacao: `GEOMETRIA_C2_CP_DECOMPOSICAO_POR_CARRY(1).md` chegou vazio na
copia de trabalho desta versao e, portanto, nao foi usado para afirmacoes.
