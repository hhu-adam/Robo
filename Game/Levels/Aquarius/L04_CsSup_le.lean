import Game.Levels.Aquarius.L03_Le_csSup

World "Aquarius"
Level 4

Title ""

Introduction "Intro Aquarius L04"

open Set FullGrind

/---/
TheoremDoc csSup_le as "csSup_le" in "sSup"

Statement {s : Set ℝ} {b c : ℝ} (hne : s.Nonempty) (h : ∀ x ∈ s, x ≤ b) (hbc : b ≤ c) :
    sSup s ≤ c := by
  Hint "[Hint cssuple] The supremum is the *least* upper bound. New theorem: `csSup_le`"
  Hint (hidden := true) "[Hint suplec] As `sSup s` is the least upper bound of `s`,
    it sits below every upper bound.
    Hypothesis `h` says `b` bounds all of `s`, hence`sSup s ≤ b`.
    Chaining with `b ≤ c` gives `sSup s ≤ c`."
  apply csSup_le
  · assumption
  intro x h1
  apply h at h1
  grind

Conclusion "Conclusion Aquarius L04: `csSup_le` bounded the supremum from above by `b`, and
transitivity of `≤` pushed it up to `c`."

NewTheorem csSup_le

TheoremTab "sSup"
