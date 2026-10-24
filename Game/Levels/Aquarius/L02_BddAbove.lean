import Game.Levels.Aquarius.L01_UpperBounds

World "Aquarius"
Level 2

Introduction "Intro Aquarius L02"

open Set

Statement (preamble := grind_mode 1) {a b : ℝ} {p : ℝ → Prop} :
    BddAbove {x ∈ Ioo a b | p x} := by
  Hint "[Hint bdad]
    Need to show that $\\\{x \\in (a,b) | p(x) \\}$ is bounded above.
    Expand `BddAbove` with `rw` and new theorem `bddAbove_def`."
  rw [bddAbove_def]
  Hint (hidden := true) "[Hint hd] `b` is an upper bound of this set. "
  use b
  Branch -- alternative solution with restricted grind
    intro y hy
    simp at hy
    have := hy.1
    unfold Ioo at this
    simp at this
    grind (ematch := 0)
  Hint "[Hint hq5jg] Remember `grind`."
  grind

/---/
TheoremDoc bddAbove_def as "bddAbove_def" in "Set"
NewTheorem bddAbove_def

Conclusion "Conclusion Aquarius L02"
