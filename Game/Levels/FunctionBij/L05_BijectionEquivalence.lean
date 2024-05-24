import Game.Metadata


World "FunctionBij"
Level 5

Title "Bijection of Equivalence"

Introduction
"
In this level you show that there every bijection gives rise to an equivalence.
"

open Function

Statement Equiv.ofBijective (f : A → B) (h : Bijective f) : A ≃ B := by
  have := bijective_iff_has_inverse.mp h
  choose g hg using this
  fconstructor
  · exact f
  · exact g
  · exact hg.left
  · exact hg.right
