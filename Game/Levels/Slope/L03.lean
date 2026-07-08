import Game.Metadata
import Mathlib.LinearAlgebra.AffineSpace.Slope

World "Slope"
Level 3

Statement {x y : ℝ} (h : x ≠ y) :
    let f : ℝ → ℝ := fun x => x ^ 2
    slope f x y = x + y := by
  rw [slope_def_field]
  grind
