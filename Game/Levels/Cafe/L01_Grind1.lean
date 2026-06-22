import Game.Metadata

World "Cafe"
Level 1

Title ""

/-
Introduction "
**Lina**:  Jetzt ich wieder.
"
-/
Introduction "Intro Cafe L01"

Statement (a b c : ℤ) :
    a + b + c = 3 →
    a ^ 2 + b ^ 2 + c ^ 2 = 5 →
    a ^ 3 + b ^ 3 + c ^ 3 = 7 →
    a ^ 4 + b ^ 4 = 9 - c ^ 4 := by
  grind

/-- To add. -/
TacticDoc grind

NewTactic grind

Conclusion "Cafe L01"
