import Game.Metadata


World "FunctionBij"
Level 4

Title "Bijection of Equivalence"

Introduction
"
In this level you show that there every bijection gives rise to an equivalence.
"

open Function

Statement Equiv.bijective (f : A ≃ B) : Bijective f.toFun := by
  constructor
  · Branch
      intro a₁ a₂ h
      simpa [congr_arg f.invFun] using h
    apply Equiv.injective
  · apply RightInverse.surjective f.right_inv

NewTheorem Function.RightInverse.surjective Equiv.injective
