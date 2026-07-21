import Game.Metadata


World "Step"
Level 4

open Finsupp

/- This level introduces `single`. -/

/---/
DefinitionDoc Finsupp.single as "Finsupp.single" in "LinearAlgebra"

/---/
TheoremDoc Finsupp.linearCombination_single as "Finsupp.linearCombination_single" in "LinearAlgebra"

Statement : linearCombination ℝ ![2, (5 : ℝ)] (single 0 1) = 2 := by
  Hint (hidden := true) "[Hint lcsgle] Try to apply the theorem `linearCombination_single`."
  rw [linearCombination_single]
  simp

NewDefinition Finsupp.single
NewTheorem Finsupp.linearCombination_single

TheoremTab "LinearAlgebra"
