import Game.Metadata

World "Espresso"
Level 3

Title ""
Statement (a c : ℝ) (h : a ≠ c): ∃ b : ℝ, a < b ∧ b < c ∨ c < b ∧ b < a := by
  Hint "It is clear which `b` can be used."
  use (a + c) / 2
  grind


Conclusion "Espresso L02"
