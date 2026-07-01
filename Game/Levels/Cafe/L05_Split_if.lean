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
Statement (x : ℤ) :
    0 ≤ if 0 ≤ x then x else -x := by
  Hint "[Hint grindSplitIf] Here `if 0 ≤ x then x else -x` is just the absolute value `|x|`, and we
  want to show it is nonnegative. The goal depends on whether `0 ≤ x` holds, so it needs a case
  split. `grind` splits on the `if` automatically and closes both branches with linear arithmetic,
  so just try `grind`."
  grind

/-- To add. -/
TacticDoc grind

NewTactic grind

Conclusion "Cafe L05"
