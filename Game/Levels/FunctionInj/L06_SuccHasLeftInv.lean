import Game.Metadata


World "FunctionInj"
Level 6

Title "Left Inverse"

Introduction
"
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

NewDefinition Function.HasLeftInverse
