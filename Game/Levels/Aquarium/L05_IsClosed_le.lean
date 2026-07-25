import Game.Levels.Aquarium.L04_CsSup_le

World "Aquarium"
Level 5

Title ""

Introduction "Intro Aquarium L04"

open Set

/---/
TheoremDoc isClosed_le as "isClosed_le" in "Topology"

Statement {f : ℝ → ℝ} {c : ℝ} (hf : Continuous f) : IsClosed {x | f x ≤ c} := by
  Hint "[Hint iscl] The goal is to show that set of points where the continuous function `f` stays
    below the constant `c` is closed.
    Apply `isClosed_le`, which says that for two continuous functions
    $f$ and $g$, the set of points `b` where $f (b) ≤ g (b)$ is  closed in $\\mathbb\{R}$."
  apply isClosed_le
  Hint "The remaining two goals are the continuity of the functions $f$ and $g$
    to which we applied `isClosed_le`.  Continuity of $f$ is an `assumption`."
  · assumption
  · Hint "For continuity of the constant function, use `fun_prop`,
      which automatically proves such function properties."
    fun_prop

Conclusion "Conclusion Aquarium L05: `isClosed_le` turns a `≤` between continuous functions into a
closed set."

NewTactic fun_prop
NewTheorem isClosed_le

TheoremTab "Topology"
