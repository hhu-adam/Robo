import Game.Metadata

World "Hamel"
Level 6

open Finsupp

Introduction "Intro Hamel L06"

/- This level introduces `linearCombination`. -/

/---/
TheoremDoc Finsupp.linearCombination_apply as "Finsupp.linearCombination_apply" in "LinearAlgebra"

/---/
TheoremDoc Finsupp.sum_fintype as "Finsupp.sum_fintype" in "LinearAlgebra"

Statement : linearCombination ℝ ![2, (5 : ℝ)] (equivFunOnFinite.symm ![1, 2]) = 12 := by
  Hint "[Hint lcapply] Unfold the linear combination with `linearCombination_apply` and
    `Finsupp.sum_fintype`."
  rw [linearCombination_apply, sum_fintype]
  · Hint "[Hint lcsum2] Now it is a sum over `Fin 2`, remember the theorem in previous level."
    rw [Fin.sum_univ_two]
    simp
    ring
  · Hint (hidden := true) "[Hint lcside] Try `simp`."
    simp

NewDefinition Finsupp.linearCombination
NewTheorem Finsupp.linearCombination_apply Finsupp.sum_fintype

TheoremTab "LinearAlgebra"
