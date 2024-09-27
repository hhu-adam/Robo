import Game.Metadata


World "FunctionSurj"
Level 6

Title "Every function with nonempty fibres has a right inverse."


Introduction
"

"

open Function

Statement {A B : Type} (f : A → B) (nonempty_fibre : ∀ b : B, ∃ (x : A), f x = b) :
    HasRightInverse f := by
  choose g hg using nonempty_fibre
  use g
  assumption

NewTactic choose
