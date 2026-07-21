import Game.Levels.Culmen.L01_UpperBounds

World "Culmen"
Level 2

Introduction "Intro Culmen L02"

open Set FullGrind

Statement {a b : ℝ} {p : ℝ → Prop} :
    BddAbove {x ∈ Ioo a b | p x} := by
  Hint "[Hint bdad] `rw` theorem `bddAbove_def` to translate the problem. "
  rw [bddAbove_def]
  Hint (hidden := true) "[Hint hd] `b` is a upper bound of this set. "
  use b
  Branch -- alternative solution with restricted grind
    intro y hy
    simp at hy
    have := hy.1
    unfold Ioo at this
    simp at this
    grind (ematch := 0)
  grind

/-- -/
TheoremDoc bddAbove_def as "bddAbove_def" in "Set"
NewTheorem bddAbove_def

Conclusion ""
