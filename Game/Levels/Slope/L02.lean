import Game.Metadata
import Mathlib.LinearAlgebra.AffineSpace.Slope

World "Slope"
Level 2

Statement {x y : ℝ} (h : x ≠ y) :
    let f : ℝ → ℝ := fun x ↦ x
    slope f x y = 1 := by
  rw [slope_def_field]
  Hint (hidden := true) "[Hint sll2] Try `grind`."
  Branch
    simp [f]
    Hint (hidden := true) "[Hint sll2] Try `grind`."
  grind
