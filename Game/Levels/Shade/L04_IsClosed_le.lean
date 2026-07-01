import Game.Levels.Shade.L03_CsSup_le

World "Shade"
Level 4

Title ""

Introduction
"
"

open Set

/-- `isClosed_le (hf : Continuous f) (hg : Continuous g) : IsClosed {b | f b ≤ g b}` -/
TheoremDoc isClosed_le as "isClosed_le" in "Topology"

Statement {f : ℝ → ℝ} {c : ℝ} (hf : Continuous f) : IsClosed {x | f x ≤ c} := by
  Hint "[Hint iscl] The goal is the set of points where the continuous function `f` stays
    below the constant `c`.  Apply `isClosed_le`."
  apply isClosed_le
  Hint "Two continuity goals remain.  Use `fun_prop`, which proves such function
    properties automatically."
  · assumption
  · Hint "The remaining goal is the continuity statement `Continuous f`. Use `fun_prop`,
      which automatically proves such function properties."
    fun_prop

Conclusion
"Well done.  `isClosed_le` turns a `≤` between continuous functions into a closed set."

/-- `fun_prop` automatically discharges function-property goals such as `Continuous`,
`Measurable`, or `Differentiable`. -/
TacticDoc fun_prop
NewTactic fun_prop

NewTheorem isClosed_le

TheoremTab "Topology"
