import Game.Levels.Culmen.L03_Le_csSup

World "Culmen"
Level 4

Title ""

Introduction
"
"

open Set FullGrind

/-- `csSup_le (hne : s.Nonempty) (H : ∀ a ∈ s, a ≤ b) : sSup s ≤ b` -/
TheoremDoc csSup_le as "csSup_le" in "sSup"

Statement {s : Set ℝ} {b c : ℝ} (hne : s.Nonempty) (h : ∀ x ∈ s, x ≤ b) (hbc : b ≤ c) :
    sSup s ≤ c := by
  Hint "[Hint suplec] This is the dual of the previous level. `sSup s` is the *least* upper bound
  of `s`, so it sits below every upper bound. Hypothesis `h` says `b` bounds all of `s`, hence
  `sSup s ≤ b`, and chaining with `b ≤ c` gives `sSup s ≤ c`."
  Hint (hidden := true) "[Hint cssuple] Perhaps, `csSup_le` is useful here."
  apply csSup_le
  · assumption
  intro x h1
  obtain h2 := h _ h1
  grind

Conclusion
"Perfect.  `csSup_le` bounded the supremum from above by `b`, and one
transitivity step pushed it up to `c`."
/- COMMENT
See comment in previous level.

*Comment resolved (Wenrong):* add a mathematic hint above the hidden hint.
-/

NewTheorem csSup_le

TheoremTab "sSup"
