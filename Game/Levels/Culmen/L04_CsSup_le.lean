import Game.Levels.Culmen.L03_Le_csSup

World "Culmen"
Level 4

Title ""

Introduction "Intro Culmen L04"

open Set FullGrind

/---/
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

Conclusion "Conclusion Culmen L04: `csSup_le` bounded the supremum from above by `b`, and
transitivity of `≤` pushed it up to `c`."

NewTheorem csSup_le

TheoremTab "sSup"
