import Game.Metadata

World "Shade"
Level 1

Introduction "Intro Shade L01"

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

/- TODO
  Add another level introducing UpperBounds, as this is needed in Boss level.
  E.g. the following very simple level:
-/
example {s : Set ℝ} {b : ℝ} (hb : b ∈ upperBounds s) : BddAbove s := by
  use b

/-- -/
DefinitionDoc BddAbove as "BddAbove" in "Set"

/-- -/
DefinitionDoc Set.Ioo as "Ioo" in "Set"
/- TODO
Either introduce Ioo earlier (with all the other intervals, perhaps?)
or an explanation of Ioo in the first hint given here.
-/

NewDefinition BddAbove Set.Ioo

/-- -/
TheoremDoc bddAbove_def as "bddAbove_def" in "Set"
NewTheorem bddAbove_def

Conclusion ""
