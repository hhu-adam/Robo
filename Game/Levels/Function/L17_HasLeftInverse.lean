import Game.Metadata

World "Function2"
Level 17

Title "Left Inverse"


Introduction
"
  A function `f : A → B` has a left inverse if there exists a function
  `g : B → A` such that `g ∘ f = id`.

  In this level, you will prove that the successor function on the natural numbers has a left inverse.

"

open Function

Statement : HasLeftInverse Nat.succ  := by
  Branch
    use Nat.pred
    unfold LeftInverse
    simp
  use (fun n ↦ n - 1)
  Branch
    unfold LeftInverse
    simp
  intro n
  rfl

  NewDefinition Function.LeftInverse Function.HasLeftInverse
