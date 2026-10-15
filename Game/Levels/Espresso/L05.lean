import Game.Metadata

World "Espresso"
Level 5

Title ""

Introduction "Intro Espresso L05"

Statement (x y : ℤ) (hy : y = if x ≤ 0 then 0 else x) :
    0 ≤ y := by
  Hint "[Hint grindSplitIf] If `x ≤ 0` then `y = 0`, so `0 ≤ y`.
        Otherwise, if `0 < x`, then `y = x`, so again `0 ≤ y`.
        Anyway, can prove this with `grind`."
  grind


Conclusion "Espresso L05"
