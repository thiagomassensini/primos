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
| `TEORIA_GEOMETRICA_DO_CARRY_E_OPERADOR_ORTOGONAL_MULTIBASE.md` | mapa de pesquisa para a formula da carta Cp e para a ponte carry--operador; nao importado como prova |
| `GENUINE_GLOBAL_GEOMETRIA_VERTICAL_MULTIPRIMA_GITHUB.md` | mapa de pesquisa para a identidade inicial e para o alvo posterior de convergencia bracketada; nao importado como prova |

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
| monomio de Dirichlet no ramo principal positivo | `Analytic.Cp.dirichletTerm` |
| separar `(p*m)^(-s)` em `p^(-s)m^(-s)` | `Analytic.Cp.dirichletTerm_alignedCenter` |
| `p` vezes a soma dos centros = `p^(1-s)` vezes o prefixo curto | `Analytic.Cp.p_mul_centerSum_dirichlet_eq_cpow_mul_prefix` |
| carta finita de Dirichlet com correcao vertical fatorada | `Analytic.Cp.finiteChart_dirichlet_eq_prefix_sub_cpow_mul_prefix` |
| Genuine inicial definido pela serie positiva | `Analytic.Cp.genuineDirichlet` |
| somabilidade de `n^(-s)` para `Re(s)>1` | `Analytic.Cp.summable_dirichletTerm_nat_add_one` |
| prefixos positivos convergem para o Genuine inicial | `Analytic.Cp.positiveDirichletPrefix_tendsto_genuineDirichlet` |
| carta finita escrita como dois prefixos da mesma serie | `Analytic.Cp.finiteChart_dirichlet_eq_two_prefixes` |
| passagem ao limite `finiteChart -> (1-p^(1-s))*Genuine` em `Re(s)>1` | `Analytic.Cp.finiteChart_dirichlet_tendsto_genuine_factor` |
| cota quadratica abstrata da segunda diferenca centrada | `Analytic.norm_centeredSecondDifference_le` |
| derivadas primeira e segunda de `x^(-s)` no eixo real positivo | `Analytic.hasDerivAt_realDirichletPower`, `Analytic.hasDerivAt_realDirichletPowerDeriv` |
| ganho de duas potencias para a segunda diferenca de `x^(-s)` | `Analytic.norm_realDirichletPower_centeredSecondDifference_le` |
| bracket Genuine Cp = soma saturada das segundas diferencas | `Genuine.Cp.bracket_eq_saturatedBracket` |
| majorante de um bloco Cp por `(k+1)^(-Re(s)-2)` | `Analytic.Cp.norm_realCpSaturatedBracket_le` |
| somabilidade absoluta da carta bracketada em `Re(s)>-1` | `Analytic.Cp.summable_norm_realCpSaturatedBracket` |
| prefixo bracketado = `Genuine.Cp.finiteChart` em cada corte | `Analytic.Cp.finiteBracketedDirichletChart_eq_finiteChart` |
| prefixos Genuine convergem para a carta bracketada em `Re(s)>-1` | `Analytic.Cp.finiteChart_dirichlet_tendsto_bracketedDirichletChart` |
| carta bracketada = fator Genuine no semiplano comum `Re(s)>1` | `Analytic.Cp.bracketedDirichletChart_eq_genuine_factor` |
| majorante uniforme somavel numa bola local do semiplano `Re(s)>-1` | `Analytic.Cp.norm_realCpSaturatedBracket_le_local`, `Analytic.Cp.summable_localCpBracketMajorant` |
| holomorfia da carta bracketada em `Re(s)>-1` | `Analytic.Cp.analyticOnNhd_bracketedDirichletChart` |
| unicidade da continuacao da identidade fator Genuine | `Analytic.Cp.bracketedDirichletChart_unique_analytic_continuation` |
| zero do fator Cp implica `Re(s)=1` | `Analytic.Cp.cpChartFactor_zero_implies_re_eq_one` |
| fator Cp nao zera no interior da faixa critica | `Analytic.Cp.cpChartFactor_ne_zero_on_genuineCriticalStrip` |
| quociente Cp recupera a serie Genuine em `Re(s)>1` | `Analytic.Cp.cpGenuineQuotient_eq_genuineDirichlet` |
| quociente Cp e holomorfo no interior da faixa | `Analytic.Cp.analyticOnNhd_cpGenuineQuotient_genuineCriticalStrip` |
| zeros da carta equivalem aos zeros do quociente Cp na faixa | `Analytic.Cp.bracketedDirichletChart_zero_iff_cpGenuineQuotient_zero` |
| identidade cruzada das cartas primas em `Re(s)>-1` | `Analytic.Cp.crossNormalizedChart_eq_swap` |
| quocientes Genuine de duas cameras primas coincidem na faixa | `Analytic.Cp.cpGenuineQuotient_eq_cpGenuineQuotient` |
| representante Genuine canonico recupera a serie em `Re(s)>1` | `Analytic.Cp.genuineContinuation_eq_genuineDirichlet` |
| representante Genuine canonico e holomorfo na faixa | `Analytic.Cp.analyticOnNhd_genuineContinuation_genuineCriticalStrip` |
| toda camera prima impar produz o mesmo representante Genuine | `Analytic.Cp.cpGenuineQuotient_eq_genuineContinuation` |
| zero de qualquer carta prima equivale a zero do Genuine canonico | `Analytic.Cp.bracketedDirichletChart_zero_iff_genuineContinuation_zero` |
| identidade Green discreta finita com endpoints literais | `Analytic.Cp.finiteGreenBulk_eq_boundary` |
| bloco Cp atua em `g_s` pelo autovalor exato `p^(-s)` | `Analytic.Cp.cpBlockGradient_eq_eigenvalue_mul` |
| fluxo Cp finito fatora pela diferenca dos autovalores refletidos | `Analytic.Cp.finiteCpGreenFlux_eq_eigenvalueDifference_mul_pairing` |
| endpoint externo refletido e `1/(M+1)` e tende a zero | `Analytic.Cp.finiteReflectedOuterEndpoint_eq_inv`, `Analytic.Cp.finiteReflectedOuterEndpoint_tendsto_zero` |
| certificado Green complexo finito deriva `flux=coefficient*energy+boundary` de duas identidades independentes | `Analytic.Cp.FiniteComplexGreenCertificate.green_identity`, `Analytic.Cp.finiteCpGreenCertificate` |
| bordo da instancia Cp finita e exatamente `1/(M+1)-1` | `Analytic.Cp.finiteCpGreenCertificate_boundary_eq_inv_sub_one` |
| normalizador de fase transforma o autovalor Cp em `p^(-delta)` real | `Analytic.Cp.cpPhaseNormalizer_mul_eigenvalue`, `Analytic.Cp.phaseNormalizedCpBlockGradient_eq_radial_mul` |
| o bloco refletido normalizado possui autovalor real `p^delta` | `Analytic.Cp.phaseNormalizedCpBlockGradient_reflected_eq_radial_mul` |
| Wronskiano normalizado fatora por `p^(-delta)-p^delta` | `Analytic.Cp.finitePhaseNormalizedCpGreenFlux_eq_radialDifference_mul_pairing` |
| diferenca radial e `2*delta` vezes cofator primo positivo | `Analytic.Cp.cpRadialDifference_eq_two_mul_delta_mul_cofactor`, `Analytic.Cp.cpRadialCofactor_pos` |
| identidade Green real assinada em corte finito e bordo literal | `Analytic.Cp.finiteSignedCpGreen_identity` |
| cada aresta refletida possui parte real positiva em `0<Re(s)<1` | `Analytic.Cp.finiteReflectedGradientEdge_re_pos` |
| pareamento refletido de todo corte nao vazio possui parte real positiva | `Analytic.Cp.finiteReflectedGradientPairing_re_pos` |
| energia radial Green finita e positiva para todo primo e corte nao vazio | `Analytic.Cp.finiteRadialGreenEnergy_pos` |
| a semente da carta canonica `p=3` e o endpoint Green interno `1` | `Analytic.Cp.seedSum_three_dirichlet_eq_one`, `Analytic.Cp.seedSum_three_eq_reflectedInnerEndpoint` |
| carta finita canonica = endpoint interno + traco bracketado finito | `Analytic.Cp.finiteBracketedDirichletChart_three_eq_inner_add_trace` |
| bordo Green acoplado = endpoint externo - carta bracketada finita | `Analytic.Cp.finiteBracketCoupledBoundary_eq_outer_sub_finiteChart` |
| identidade Green finita permanece exata depois de acoplar o mesmo traco ao fluxo e ao bordo | `Analytic.Cp.finiteBracketCoupledCpGreen_identity` |
| num zero Genuine, o bordo bracketado complexo e real converge a zero | `Analytic.Cp.finiteBracketCoupledBoundary_tendsto_zero_of_genuine_zero`, `Analytic.Cp.finiteBracketCoupledSignedBoundary_tendsto_zero_of_genuine_zero` |
| adicionar uma aresta adiciona seu somador e torna monotona a parte real do pareamento | `Analytic.Cp.finiteReflectedGradientPairing_succ`, `Analytic.Cp.finiteReflectedGradientPairing_re_monotone` |
| fluxo acoplado = bulk orientado + bordo bracketado | `Analytic.Cp.finiteBracketCoupledCpGreenFlux_eq_oriented_add_boundary` |
| fatoracao radial exata do fluxo acoplado | `Analytic.Cp.finiteBracketCoupledCpGreenFlux_eq_radialDifference_mul_pairing` |
| em zeros Genuine, fluxo acoplado tende a zero exatamente na linha critica | `Analytic.Cp.coupledFlux_tendsto_zero_iff_criticalDisplacement_eq_zero` |
| bloco angular canonico usa os pesos residuais `1,2,0` do traco `n mod 3` | `Analytic.Cp.canonicalAngularGradientBlock`, `Analytic.Cp.canonicalAngularWeight_eq_globalResidue` |
| carta bracketada finita `p=3` = traco angular finito + endpoint `(3M+1)^(-s)` | `Analytic.Cp.finiteBracketedDirichletChart_three_eq_angularTrace_add_outer` |
| para `Re(s)>0`, o traco angular finito converge para a carta bracketada | `Analytic.Cp.finiteCanonicalAngularTrace_tendsto` |
| em zeros Genuine da faixa, o traco angular finito converge a zero | `Analytic.Cp.finiteCanonicalAngularTrace_tendsto_zero_of_genuine_zero` |
| identidade Green assinada, energia positiva e bordo fechado implicam `delta=0` | `Analytic.Cp.SignedGreenCertificate.criticalDisplacement_eq_zero_of_genuine_zero` |
| certificado Green concreto produz a ponte Genuine--ramo | `Analytic.Cp.SignedGreenCertificate.toGenuineBranchBridge` |
| ponte ainda aberta de zeros Genuine para a norma | `Analytic.Cp.GenuineBranchBridge` (sem instancia) |
| diferenciar `bracket = centerBlock - p*center` resolve `p` vezes o gradiente central | `Analytic.Cp.cpGenuineResolvedGradient_eq_p_mul_alignedCenterGradient` |
| o residual Genuine diferenciado e normalizado e literalmente `cpBlockGradient` | `Analytic.Cp.cpGenuineGreenGradient_eq_cpBlockGradient` |
| a forma Green finita existente e exatamente a forma Green Genuine normalizada | `Analytic.Cp.finiteGenuineCpGreenFlux_eq_finiteCpGreenFlux` |
| o fluxo Genuine orientado e a diagonal TFVD sao o mesmo objeto | `Analytic.Cp.finiteOrientedGenuineCpGreenFlux_eq_tfvdDiagonal` |
| fluxo acoplado = parte real do Green Genuine orientado + bordo bracketado | `Analytic.Cp.finiteBracketCoupledCpGreenFlux_eq_genuineOriented_add_boundary` |
| bracket local C2 = segunda diferenca centrada de raio 1 | `Genuine.C2.bracket_eq_centeredSecondDifference`, `Genuine.C2.bracket_operator_eq_centeredSecondDifference` |
| bracket Cp de primo impar = soma saturada das segundas diferencas admissiveis | `Genuine.Cp.bracket_operator_eq_saturatedBracket` |
| camera local p=3 = stencil C2 de raio 1 | `Genuine.Cp.bracket_three_eq_centeredSecondDifference`, `Genuine.Cp.bracket_three_eq_c2Bracket` |
| cada par do tilt = segunda diferenca do perfil transversal | `Analytic.Cp.cpPairTilt_eq_centeredSecondDifference` |
| tilt Cp = bracket Genuine aplicado ao perfil transversal | `Analytic.Cp.cpTilt_eq_genuineBracket`, `Analytic.Cp.cpTilt_eq_saturatedBracket` |
| carta bracketada = semente + serie universal de segundas diferencas | `Analytic.Cp.bracketedDirichletChart_eq_centeredSecondDifferenceSeries` |
| quociente Genuine = serie de segundas diferencas normalizada pelo fator da camera | `Analytic.Cp.cpGenuineQuotient_eq_centeredSecondDifferenceSeries` |
| formula explicita p=3 do Genuine continuado | `Analytic.Cp.genuineContinuation_eq_centeredSecondDifferenceSeries` |
| cortes finitos de qualquer camera convergem ao fator vezes o Genuine canonico no strip | `Analytic.Cp.finiteChart_dirichlet_tendsto_factor_mul_genuineContinuation_on_strip` |
| zero Genuine no strip = cancelamento da semente 1 pela serie de segundas diferencas | `Analytic.Cp.genuineContinuation_zero_iff_centeredSecondDifferenceSeries_eq_neg_one` |
| kernel escalado da sintese tem soma zero e primitiva com endpoints nulos | `Analytic.Cp.finitePortSynthesisKernelValue_sum_eq_zero`, `Analytic.Cp.finitePortSynthesisKernelPrefix_cutoff` |
| observavel escalar mais setor fechado recuperam o pareamento diagonal | `Analytic.Cp.finitePortSynthesis_pairing_ledger` |
| ledger Wronskiano exato `M W_scalar + W_kernel = M^2 W_diagonal` | `Analytic.Cp.finiteScalarPortWronskian_synthesis_ledger` |
| off-diagonal e determinado pelo setor fechado e pela diagonal | `Analytic.Cp.finiteOffDiagonalPortWronskian_synthesis_ledger` |
| traco angular = sintese finita das segundas diferencas menos endpoint externo | `Analytic.Cp.finiteCanonicalAngularTrace_eq_secondDifferenceSynthesis_sub_outer` |
| ledger angular Green separa energia, correcao local e kernel da sintese | `Analytic.Cp.finiteCanonicalAngularScalarPairing_synthesis_green_ledger`, `Analytic.Cp.finiteCanonicalAngularGreenCorrection_synthesis_ledger` |
| primitiva do kernel = prefixo parcial escalado menos observavel completo | `Analytic.Cp.finitePortSynthesisKernelPrefix_eq_scaled_prefix_sub_cutoff`, `Analytic.Cp.finiteCanonicalAngularKernelPrefix_eq_centered_traces` |
| somacao por partes do setor fechado nao deixa endpoints | `Analytic.Cp.finitePortSynthesisKernelPairing_summation_by_parts` |
| pareamento do kernel = tamanho do corte vezes bulk fechado | `Analytic.Cp.finitePortSynthesisKernelPairing_eq_mul_closedBulk`, `Analytic.Cp.finiteCanonicalAngularSynthesisKernelPairing_eq_mul_closedBulk` |
| correcao angular = crescimento Green mais defeito local--bulk fechado | `Analytic.Cp.finiteCanonicalAngularGreenCorrection_eq_diagonalGrowth_add_closedBulkDefect` |
| observavel escalar = `M * Green + defeito fechado` | `Analytic.Cp.finiteCanonicalAngularScalarPairing_eq_mul_green_add_closedBulkDefect` |
| zero Genuine fecha exatamente o novo orcamento de bulk | `Analytic.Cp.finiteCanonicalAngularMulGreenAddClosedBulkDefect_tendsto_zero_of_genuine_zero`, `Analytic.Cp.finiteCanonicalAngularRadialClosedBulkBudget_tendsto_zero_of_genuine_zero` |
| o cancelamento local--bulk nao e identidade universal | `Analytic.Cp.finiteCanonicalAngularClosedBulkDefect_one_two_ne_zero` |
| bloco angular = bracket Genuine local mais cobordo dos vertices externos | `Analytic.Cp.canonicalAngularGradientBlock_eq_bracket_add_coboundary` |
| observavel angular escalar converge em todo o strip, sem hipotese de zero | `Analytic.Cp.finiteCanonicalAngularScalarPairing_tendsto` |
| defeito fechado = observavel escalar menos crescimento Green | `Analytic.Cp.finiteCanonicalAngularClosedBulkDefect_eq_scalar_sub_mul_green` |
| parte real do defeito fechado tende a menos infinito em todo o strip | `Analytic.Cp.finiteCanonicalAngularClosedBulkDefect_re_tendsto_atBot` |

Observacao: `GEOMETRIA_C2_CP_DECOMPOSICAO_POR_CARRY(1).md` chegou vazio na
copia de trabalho desta versao e, portanto, nao foi usado para afirmacoes.
