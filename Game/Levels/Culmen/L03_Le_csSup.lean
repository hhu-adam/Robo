import Game.Levels.Culmen.L02_BddAbove

World "Culmen"
Level 3

Title ""

Introduction
"
"

open Set FullGrind

/-- `le_csSup (hbd : BddAbove s) (hx : a ∈ s) : a ≤ sSup s` -/
TheoremDoc le_csSup as "le_csSup" in "sSup"

Statement {s : Set ℝ} {c x : ℝ} (hbd : BddAbove s) (hx : x ∈ s) (hcx : c < x) :
    c < sSup s := by
  Hint "[Hint cslt] Since `s` is bounded above, its supremum `sSup s` is an *upper bound* of `s`,
  so it dominates every element of `s` — in particular your `x ∈ s` gives `x ≤ sSup s`."
  have : x ≤ sSup s := by
    Hint (hidden := true) "[Hint lecssup] Perhaps, `le_csSup` is helpful here. "
    apply le_csSup
    · assumption
    · assumption
  grind

Conclusion
"Nicely done.  `le_csSup` turned membership `x ∈ s` into the bound
`x ≤ sSup s`, and one transitivity step finished the job."
/- COMMENT
Don't assume you know what the player did. It's fine to give another summary of
`le_csSup`, but don't write "and one transitivity step …" – the player might have needed 10 steps,
going around in circles, before they got here.

*Comment Resolved (Wenrong):* I add a Hint above the first step.
-/


NewTheorem le_csSup

/-- -/
DefinitionDoc SupSet.sSup as "sSup" in "sSup"
NewDefinition SupSet.sSup

TheoremTab "sSup"
