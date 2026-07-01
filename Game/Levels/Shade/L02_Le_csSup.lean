import Game.Levels.Shade.L01_BddAbove

World "Shade"
Level 2

Title ""

Introduction
"
"

open Set FullGrind

/-- `le_csSup (hbd : BddAbove s) (hx : a ∈ s) : a ≤ sSup s` -/
TheoremDoc le_csSup as "le_csSup" in "sSup"

Statement {s : Set ℝ} {c x : ℝ} (hbd : BddAbove s) (hx : x ∈ s) (hcx : c < x) :
    c < sSup s := by
  have : x ≤ sSup s := by
    Hint "[Hint lecssup] Perhaps, `le_csSup` is helpful here. "
    apply le_csSup
    · assumption
    · assumption
  grind

Conclusion
"Nicely done.  `le_csSup` turned membership `x ∈ s` into the bound
`x ≤ sSup s`, and one transitivity step finished the job."

NewTheorem le_csSup

/-- -/
DefinitionDoc SupSet.sSup as "sSup" in "sSup"
NewDefinition SupSet.sSup

TheoremTab "sSup"
