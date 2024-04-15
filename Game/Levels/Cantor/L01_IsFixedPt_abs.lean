import Game.Metadata
import Game.Metadata.StructInstWithHoles


World "Cantor"
Level 1

Title "Cantor"

Introduction
"
For an endo-function `f : α → α` the proposition `IsFixedPt f x` asserst that `x` is a fixed point
of `f`, that is `f x = x`.
"

open Function Set

Statement : ∀ (x : ℝ), IsFixedPt abs x ↔ 0 ≤ x := by
  intro x
  constructor
  · intro h
    rw [← h]
    --simp only [abs_nonneg]
    positivity
  · intro h
    dsimp [IsFixedPt]
    rw [abs_of_nonneg h]
