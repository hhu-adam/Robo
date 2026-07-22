import Game.Metadata

World "Step"
Level 7

open Finsupp

Statement :
    let f : ℝ → ℝ := fun x ↦ x + 2
    let g : ℝ → ℝ := fun x ↦ x - 3
    linearCombination ℝ ![f, g] (equivFunOnFinite.symm ![2, 3]) =
      fun x ↦ 5 * x - 5 := by
  rw [linearCombination_apply]
  rw [sum_fintype]
  · rw [Fin.sum_univ_two]
    simp
    funext x
    simp
    Hint "[Hint ringt]`ring` sees through the `let`-definitions of `f` and `g`,
      so it can close the goal on its own."
    ring
  · simp
