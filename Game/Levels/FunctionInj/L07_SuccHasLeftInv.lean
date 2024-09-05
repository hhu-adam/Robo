import Game.Metadata


World "FunctionInj"
Level 7

Title "Left Inverse"

Introduction
"
In this level, you will prove that the successor function on the natural numbers has a left inverse.

"

open Function

Statement : HasLeftInverse Nat.succ  := by
  Branch
    use (fun n ↦ n - 1)
    simp [LeftInverse]
  use (fun n ↦ if 0 < n then n - 1 else 0)
  unfold LeftInverse
  simp

NewDefinition Function.HasLeftInverse
