import Game.MetaData

World "Shade"
Level 1

open Set FullGrind

Statement {a b : ℝ} {p : ℝ → Prop} :
    BddAbove {x ∈ Ioo a b | p x} := by
  Hint "[Hint bdad] `rw` theorem `bddAbove_def` to translate the problem. "
  rw [bddAbove_def]
  Hint (hidden := true) "[Hint hd] `b` is a upper bound of this set. "
  use b
  grind

/-- -/
DefinitionDoc BddAbove as "BddAbove" in "Set"

/-- -/
DefinitionDoc Set.Ioo as "Ioo" in "Set"

NewDefinition BddAbove Set.Ioo

/-- -/
TheoremDoc bddAbove_def as "bddAbove_def" in "Set"
NewTheorem bddAbove_def
