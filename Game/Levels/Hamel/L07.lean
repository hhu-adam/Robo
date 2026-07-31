import Game.Metadata

World "Hamel"
Level 7

open Finsupp

Statement :
    let f : ℝ → ℝ := fun x ↦ x + 2
    let g : ℝ → ℝ := fun x ↦ x - 3
    linearCombination ℝ ![f, g] (equivFunOnFinite.symm ![2, 3]) =
      fun x ↦ 5 * x - 5 := by
  Hint "[Hint lc2fun] This time the vectors are the two functions
    $$
    \\begin\{aligned}
      f &\\colon ℝ \\to ℝ, \\quad x \\mapsto x + 2, \\\\ %
      g &\\colon ℝ \\to ℝ, \\quad x \\mapsto x - 3,
    \\end\{aligned}
    $$
    and you have to compute their linear combination `2 • f + 3 • g`. Unfold it the same
    way as in the previous level."
  Hint (hidden := true) "[] Rewrite the goal using `linearCombination_apply` to unfold the
    definition of `linearCombination` and `sum_fintype` to transform the summation."
  rw [linearCombination_apply]
  rw [sum_fintype]
  · Hint (hidden := true) "[] Remember the theorem `Fin.sum_univ_two`."
    rw [Fin.sum_univ_two]
    Hint "[] Use `simp` to simplify "
    simp
    funext x
    simp
    Hint "[Hint ringt]`ring` sees through the `let`-definitions of `f` and `g`,
      so it can close the goal on its own."
    ring
  · simp
