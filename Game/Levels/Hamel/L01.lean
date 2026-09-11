import Game.Metadata

World "Hamel"
Level 1

Introduction "Intro Hamel L01"

Statement (a b c : ℝ) : ![a, b, c] 0 + ![a, b, c] 1 = a + b := by
  Hint "[Hint s1trl] An `n`-dimensional vector is a function out of `Fin n`. For instance
  a real-valued vector `x : Fin n → ℝ` assigns to each coordinate `i : Fin` a scalar
  `x i : ℝ`. We represent such a vector as `![x_1, …, x_n]`."
  Hint (hidden := true) "`rfl`?"
  rfl

NewDefinition vecNotation
