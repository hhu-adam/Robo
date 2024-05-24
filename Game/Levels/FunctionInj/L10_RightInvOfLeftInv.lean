import Game.Metadata


World "FunctionInj"
Level 10

Title "Injections with nonempty domain have retract."


Introduction
"
  In this level you show that an injective function with a nonempty domain has a left inverse.
"

open Function Set

#check rightInverse_of_injective_of_leftInverse

theorem rightInverse_of_injective_of_leftInverse {f : α → β} {g : β → α} (injf : Injective f)
    (hL : LeftInverse f g) : RightInverse f g := by
  intro x
  have h : f (g (f x)) = f x := by
    rw [hL]
  Branch
    apply injf at h
    assumption
  apply injf
  assumption

NewTheorem rightInverse_of_injective_of_leftInverse
