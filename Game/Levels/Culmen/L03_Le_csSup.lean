import Game.Levels.Culmen.L02_BddAbove

World "Culmen"
Level 3

Title ""

Introduction "Intro Culmen L03"

open Set FullGrind

/---/
TheoremDoc le_csSup as "le_csSup" in "sSup"

Statement {s : Set ℝ} {c x : ℝ} (hbd : BddAbove s) (hx : x ∈ s) (hcx : c < x) :
    c < sSup s := by
  Hint "[Hint cslt] Since `s` is bounded above, its supremum `sSup s` is an upper bound of s.
  So `x ∈ s` implies `x ≤ sSup s`."
  have : x ≤ sSup s := by
    Hint (hidden := true) "[Hint lecssup] Perhaps, `le_csSup` is helpful here. "
    apply le_csSup
    · assumption
    · assumption
  grind

Conclusion "Conclusion Culmen L03: `le_csSup` turned membership `x ∈ s` into the bound
`x ≤ sSup s`, and transitivity of `≤` finished the job."

NewTheorem le_csSup
NewDefinition SupSet.sSup

TheoremTab "sSup"
