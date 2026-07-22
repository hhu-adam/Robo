import Game.Metadata

World "Slope"
Level 7

open Topology Filter Metric FullGrind Set


Introduction "[Intro] The same inequality `𝓝[≠] 0 ≤ 𝓝 0` has a one-line proof.

The previous level reconstructed it from `nhdsWithin_mono`.  In fact Mathlib records the general
fact directly: a neighbourhood filter within any set is at most the full neighbourhood filter.  This
is `nhdsWithin_le_nhds`, and it is the form we use throughout the rest of the planet.
"

/---/
TheoremDoc nhdsWithin_le_nhds as "nhdsWithin_le_nhds" in "Function"

Statement : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 := by
  Hint "[Hint csrcg] Can also prove this directly with `nhdsWithin_le_nhds`."
  apply nhdsWithin_le_nhds

Conclusion ""

NewTheorem nhdsWithin_le_nhds
