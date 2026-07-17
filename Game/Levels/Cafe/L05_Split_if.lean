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
    0 ≤ if x ≤ 0 then 0 else x := by
  Hint "[Hint grindSplitIf] Here `if x ≤ 0 then 0 else x` and we
  want to show it is nonnegative. The goal depends on whether `x ≤ 0` holds, so it needs a case
  split. `grind` splits on the `if` automatically and closes both branches with linear arithmetic,
  so just try `grind`."
  grind

NewTactic grind

Conclusion "Cafe L05"
