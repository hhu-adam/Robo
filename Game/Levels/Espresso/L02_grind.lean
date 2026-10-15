import Game.Metadata

World "Espresso"
Level 2

Title ""

Introduction "Intro Espresso L02"

Statement (a c : ℝ) (h : a ≠ c) : a < c ∨ c < a := by
  Hint "[Hint 53n7o] New tactic: `grind`"
  grind

NewTactic grind

Conclusion "Espresso L02"
