import Game.Metadata


World "Step"
Level 2

open Finsupp

/- This level introduces `Fin.sum_univ_two`. -/

/---/
TheoremDoc Fin.sum_univ_two as "Fin.sum_univ_two" in "LinearAlgebra"

Statement : ∑ i : Fin 2, ![3, (7 : ℝ)] i = 10 := by
  Hint "[Hint fsuniv2] `Fin.sum_univ_two` rewrites a sum over `Fin 2` into its
    two summands: `∑ i, f i = f 0 + f 1`."
  rw [Fin.sum_univ_two]
  simp
  ring

NewTheorem Fin.sum_univ_two

TheoremTab "LinearAlgebra"
