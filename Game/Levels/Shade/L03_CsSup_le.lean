import Game.Levels.Shade.L02_Le_csSup

World "Shade"
Level 3

Title ""

Introduction
"
"

open Set FullGrind

/-- `csSup_le (hne : s.Nonempty) (H : ∀ a ∈ s, a ≤ b) : sSup s ≤ b` -/
TheoremDoc csSup_le as "csSup_le" in "sSup"

Statement {s : Set ℝ} {b c : ℝ} (hne : s.Nonempty) (H : ∀ x ∈ s, x ≤ b) (hbc : b ≤ c) :
    sSup s ≤ c := by
  Hint "[Hint cssuple] Perhaps, `csSup_le` is useful here."
  apply csSup_le
  · assumption
  intro x h
  obtain h1 := H _ h
  grind

Conclusion
"Perfect.  `csSup_le` bounded the supremum from above by `b`, and one
transitivity step pushed it up to `c`."

NewTheorem csSup_le

TheoremTab "sSup"
