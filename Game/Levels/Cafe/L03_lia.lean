import Game.Metadata

World "Cafe"
Level 3

Title ""

/-
Introduction "
**Lina**:  Jetzt ich wieder.
"
-/
Introduction "Intro Cafe L01"

/- this level used to teach that grind can solve some linear arithmetic problem. -/
Statement {x y : ℤ} : 2 * x + 4 * y ≠ 5 := by
  grind

/-- To add. -/
TacticDoc grind

NewTactic grind

Conclusion "Cafe L03"
