import Game.Metadata

World "Cafe"
Level 6

Title ""

/-
Introduction "
**Lina**:  Jetzt ich wieder.
"
-/
Introduction "Intro Cafe L06"

/- this level used to teach that grind can solve some linear arithmetic problem. -/
Statement {x y : ℤ} : 2 * x + 4 * y ≠ 5 := by
  Hint "[Hint grindLia] The left-hand side `2 * x + 4 * y` is always even, while `5` is odd, so they
  can never be equal. `grind` can reason about such linear integer arithmetic on its own, so just
  try `grind`."
  grind

/-- To add. -/
TacticDoc grind

NewTactic grind

Conclusion "Cafe L06"
