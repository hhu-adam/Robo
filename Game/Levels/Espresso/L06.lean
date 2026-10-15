import Game.Metadata

World "Espresso"
Level 6

Title ""

Introduction "Intro Espresso L06"

Statement {x y : ℤ} : 2 * x + 4 * y ≠ 5 := by
  Hint "[Hint grindLia] The left-hand side `2 * x + 4 * y` is always even, while `5` is odd, so they
  can never be equal. `grind` can reason about such linear integer arithmetic on its own, so just
  try `grind`."
  grind

Conclusion "Espresso L06"
