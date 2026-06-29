import Game.Metadata

World "Cafe"
Level 5

Title ""

/-
Introduction "
**Lina**:  Jetzt ich wieder.
"
-/
Introduction "Intro Cafe L05"

/- this level used to teach that grind can split ifs. -/
Statement (c : Bool) (x y : Nat)
    (h : (if c then x else y) = 0) :
    x = 0 ∨ y = 0 := by
  grind

/-- To add. -/
TacticDoc grind

NewTactic grind

Conclusion "Cafe L05"
