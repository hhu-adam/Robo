import Game.Metadata

World "Espresso"
Level 2

Title ""

Introduction "Intro Espresso L02: `grind`"

Statement (a c : ℝ) (h : a ≠ c) : a < c ∨ c < a := by
  grind

NewTactic grind

Conclusion "Conclusion Espresso L02"
