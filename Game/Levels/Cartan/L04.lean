import Game.Metadata

World "Cartan"
Level 4

open Topology Filter

Statement : ∀ᶠ x in atTop, x ≥ 1066 := by
  Hint "[Hint zntfk] For a filter `𝓕`, `∀ᶠ x in 𝓕, p x` says that `p x` holds *eventually*
    i.e. the set `\{x | p x}` is a member of 𝓕."
  Hint (hidden := true) "[Hint ysocy] Remember `mem_atTop`"
  apply mem_atTop

NewDefinition Filter.Eventually
