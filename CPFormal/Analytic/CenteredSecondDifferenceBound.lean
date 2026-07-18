import Mathlib

/-!
# Ganho quadratico da segunda diferenca central

Este arquivo isola o mecanismo analitico minimo usado pelas cartas
bracketadas. Se a segunda derivada de `f : R -> C` tem norma limitada por
`C` a direita de `lower`, entao o bracket de raio nao negativo `radius`
satisfaz

`||f (center-radius) - 2 f center + f (center+radius)||
    <= 2 C radius^2`.

A prova usa duas vezes a desigualdade do valor medio para funcoes com valores
em um espaco normado. O fator `radius^2` e o ganho que, para `f(x)=x^(-s)`,
desloca a barreira de convergencia de `re(s)>1` para `re(s)>-1`.
-/

namespace CPFormal.Analytic

noncomputable section

local instance : NormedSpace ℝ ℂ := NormedSpace.complexToReal

/--
Uma cota uniforme para a segunda derivada produz o ganho quadratico de uma
segunda diferenca central. A formulacao usa derivadas ordinarias nos pontos
de `Set.Ici lower`; nas duas aplicacoes do valor medio elas sao restringidas
automaticamente ao conjunto convexo relevante.
-/
theorem norm_centeredSecondDifference_le
    {f f' f'' : ℝ → ℂ} {lower center radius C : ℝ}
    (hradius : 0 ≤ radius)
    (hleft : lower ≤ center - radius)
    (hf : ∀ x, lower ≤ x → HasDerivAt f (f' x) x)
    (hf' : ∀ x, lower ≤ x → HasDerivAt f' (f'' x) x)
    (hbound : ∀ x, lower ≤ x → ‖f'' x‖ ≤ C) :
    ‖f (center - radius) - (2 • f center) + f (center + radius)‖ ≤
      2 * C * radius ^ 2 := by
  have hC : 0 ≤ C :=
    le_trans (norm_nonneg (f'' (center - radius)))
      (hbound (center - radius) hleft)

  let g : ℝ → ℂ := fun t ↦
    f (center - t) + f (center + t) - (2 • f center)

  have hfirstDifference :
      ∀ t ∈ Set.Icc (0 : ℝ) radius,
        ‖f' (center + t) - f' (center - t)‖ ≤ 2 * C * radius := by
    intro t ht
    have hminus : lower ≤ center - t := by linarith [ht.2]
    have hplus : lower ≤ center + t := by linarith [ht.1]
    have hlip :=
      (convex_Ici lower).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun x hx ↦ (hf' x hx).hasDerivWithinAt)
        hbound hminus hplus
    calc
      ‖f' (center + t) - f' (center - t)‖ ≤
          C * ‖(center + t) - (center - t)‖ := hlip
      _ = C * (2 * t) := by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · ring
        · linarith [ht.1]
      _ ≤ 2 * C * radius := by nlinarith [ht.2]

  have hg :
      ∀ t ∈ Set.Icc (0 : ℝ) radius,
        HasDerivWithinAt g
          (f' (center + t) - f' (center - t))
          (Set.Icc (0 : ℝ) radius) t := by
    intro t ht
    have hminusPoint : lower ≤ center - t := by linarith [ht.2]
    have hplusPoint : lower ≤ center + t := by linarith [ht.1]
    have hinnerMinus :
        HasDerivAt (fun u : ℝ ↦ center - u) (-1 : ℝ) t := by
      exact (hasDerivAt_id' t).const_sub center
    have hinnerPlus :
        HasDerivAt (fun u : ℝ ↦ center + u) (1 : ℝ) t := by
      exact (hasDerivAt_id' t).const_add center
    have hminus :
        HasDerivAt (fun u : ℝ ↦ f (center - u))
          (-f' (center - t)) t := by
      simpa [Function.comp_def] using
        (hf (center - t) hminusPoint).scomp t hinnerMinus
    have hplus :
        HasDerivAt (fun u : ℝ ↦ f (center + u))
          (f' (center + t)) t := by
      simpa [Function.comp_def] using
        (hf (center + t) hplusPoint).scomp t hinnerPlus
    have hsum :
        HasDerivAt
          (fun u : ℝ ↦ f (center - u) + f (center + u))
          (-f' (center - t) + f' (center + t)) t :=
      hminus.fun_add hplus
    have hsumConst := hsum.sub_const (2 • f center)
    simpa only [g, sub_eq_add_neg, neg_add_rev, add_comm] using
      hsumConst.hasDerivWithinAt

  have houter :=
    (convex_Icc (0 : ℝ) radius).norm_image_sub_le_of_norm_hasDerivWithin_le
      hg hfirstDifference
      (show (0 : ℝ) ∈ Set.Icc 0 radius by exact ⟨le_rfl, hradius⟩)
      (show radius ∈ Set.Icc (0 : ℝ) radius by exact ⟨hradius, le_rfl⟩)

  have hleftNorm :
      ‖g radius - g 0‖ =
        ‖f (center - radius) - (2 • f center) +
          f (center + radius)‖ := by
    simp only [g]
    congr 1
    simp only [sub_zero, two_smul]
    abel_nf

  rw [hleftNorm] at houter
  calc
    ‖f (center - radius) - (2 • f center) +
        f (center + radius)‖ ≤
        (2 * C * radius) * ‖radius - 0‖ := houter
    _ = 2 * C * radius ^ 2 := by
      rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hradius]
      ring

end

end CPFormal.Analytic
