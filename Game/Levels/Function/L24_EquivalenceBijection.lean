import Game.Metadata



World "Function2"
Level 24

Title "Bijection of Equivalence"

Introduction
"
In this level you show that there every bijection gives rise to an equivalence.
"

open Function

Statement Equiv.bijective (f : A ≃ B) : Bijective f.toFun := by
  constructor
  · Branch
      apply Equiv.injective
    intro a₁ a₂ h
    simpa [congr_arg f.invFun] using h
  · apply RightInverse.surjective f.right_inv
