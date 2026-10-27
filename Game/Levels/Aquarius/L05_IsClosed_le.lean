import Game.Levels.Aquarius.L04_CsSup_le

World "Aquarius"
Level 5

Title ""

Introduction "Intro Aquarius L05"

open Set

/---/
TheoremDoc isClosed_le as "isClosed_le" in "Topology"

Statement {f : ℝ → ℝ} {c : ℝ} (hf : Continuous f) : IsClosed {x | f x ≤ c} := by
  Hint "[Hint iscl]
    `Continuous f` means that `f` is continuous.
    `IsClosed s` means that the set `s` is closed (as a subset of `ℝ`).
    So the goal is to show that set of points where the continuous function `f` stays
    below the constant `c` is closed.
    Apply new theorem `isClosed_le`, which says that for two continuous functions
    $f$ and $g$, the set of points `b` where $f (b) ≤ g (b)$ is closed in $\\mathbb\{R}$."
  apply isClosed_le
  Hint "The remaining two goals are the continuity of the functions `f` and `g`
    to which we applied `isClosed_le`.
    Use `assumption` or new tactic `fun_prop` to show this for f.
    Use fun_prop to show this for the constant function."
  · fun_prop --assumption
  · fun_prop

Conclusion "Conclusion Aquarius L05: `isClosed_le` turns a `≤` between continuous functions into a
closed set."

NewTactic fun_prop
NewTheorem isClosed_le

NewDefinition Continuous

TheoremTab "Topology"
