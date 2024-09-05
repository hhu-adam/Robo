import Game.Metadata


World "FunctionInj"
Level 8

Title "Injections with nonempty domain have retract."


Introduction
"
"

open Function Set

-- This is in Mathlib: #check rightInverse_of_injective_of_leftInverse
Statement {A B : Type} {f : A → B} {g : B → A} (injf : Injective f)
    (hL : LeftInverse f g) : RightInverse f g := by
  intro x
  apply injf
  rw [hL]
