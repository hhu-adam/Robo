import Game.Levels.Mono.L07_SuccHasLeftInv

World "Mono"
Level 8

Title "" -- ""


Introduction ""

open Function Set

-- This is in mathlib: #check rightInverse_of_injective_of_leftInverse
Statement {A B : Type} {f : A → B} {g : B → A} (injf : Injective f)
    (hL : LeftInverse f g) : RightInverse f g := by
  Hint "**Du**: Was steht hier?

  **Robo**:  Eine injektive Abbildung `f`, die zu einer Abbildung `g` linksinvers ist, ist zur selben Abbildung auch rechtsinvers.
  "
  intro x
  apply injf
  rw [hL]
