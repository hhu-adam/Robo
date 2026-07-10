import Game.Metadata

World "Slope"
Level 7

open Topology Filter

/---/
TheoremDoc nhdsWithin_mono as "nhdsWithin_mono" in "Function"

/---/
DefinitionDoc Set.Ioi as "Set.Ioi" in "Set"

/---/
DefinitionDoc Set.Iio as "Set.Iio" in "Set"

Statement : 𝓝[>] (0:ℝ) ≤ 𝓝[≠] 0 ∧ 𝓝[<] (0 : ℝ) ≤ 𝓝[≠] 0 := by
  Hint "[Hint nwmono] Both sides restrict the points near `0` to a set:
    `𝓝[≠] 0` is `nhdsWithin 0 \{0}ᶜ`, and `𝓝[>] 0` is
    `nhdsWithin 0 (Set.Ioi 0)`, where `Set.Ioi 0` is the interval
    `(0, ∞)`. Since `Set.Ioi 0 ⊆ \{0}ᶜ`, the theorem `nhdsWithin_mono`
    does the job."
  constructor
  · apply nhdsWithin_mono
    Hint (hidden := true) "[Hint nwmgr] `grind` can prove this inclusion."
    grind
  · apply nhdsWithin_mono
    grind

NewTheorem nhdsWithin_mono
NewDefinition Set.Ioi Set.Iio
