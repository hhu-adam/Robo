import Game.Metadata

World "Cartan"
Level 4

open Topology Filter

/-- `∀ᶠ x in f, p x` says that `p x` holds *eventually* along the filter `f`,
i.e. the set `{x | p x}` is a member of `f`. -/
DefinitionDoc Filter.Eventually as "∀ᶠ"

/---/
TheoremDoc eventually_lt_nhds as "eventually_lt_nhds"

Statement {a : ℝ} (hab : a < 0) :
    ∀ᶠ x in 𝓝 a, x < 0 := by
  apply eventually_lt_nhds
  assumption

NewTheorem eventually_lt_nhds
NewDefinition Filter.Eventually
