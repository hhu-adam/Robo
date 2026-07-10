import Game.Metadata

World "Slope"
Level 6

open Topology Filter Metric

/---/
TheoremDoc nhdsWithin_le_nhds as "nhdsWithin_le_nhds" in "Function"

Statement : 𝓝[≠] 0 ≤ 𝓝 0 := by
  Hint "[Hint nwln] `𝓝[≠] 0` is notation for `nhdsWithin 0 \{0}ᶜ`: the points
    near `0` that lie in the set `\{0}ᶜ`, i.e. everything near `0` except `0`
    itself. So it sees fewer points than `𝓝 0` — that is what `≤` says here.
    This is exactly the theorem `nhdsWithin_le_nhds`; apply it."
  apply nhdsWithin_le_nhds

NewTheorem nhdsWithin_le_nhds
