import Game.Metadata

World "Cafe"
Level 8

Title ""

open Set Filter Topology FullGrind

Statement : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] 0 := by
  Hint "[Hint nhdsmno] The right neighborhood is smaller than the punctured neighborhood.
  Apply `nhdsWithin_mono`. "
  apply nhdsWithin_mono
  Hint (hidden := true) "[Hint tg8nh] Try `grind`. "
  grind

/---/
TheoremDoc nhdsWithin_mono as "nhdsWithin_mono" in "Topology"

NewTheorem nhdsWithin_mono

/---/
DefinitionDoc Set.Ioi as "Set.Ioi" in "Set"

/---/
DefinitionDoc Set.Iio as "Set.Iio" in "Set"

/-- `𝓝[s] a` is the neighborhood of `a` *inside* the set `s`:
take a neighborhood of `a` and keep only the points that lie in `s`.

Two special cases:

* `𝓝[>] (0 : ℝ)` is short for `𝓝[Set.Ioi 0] 0`: the points near `0` that are
  *greater* than `0`, i.e. a small interval `(0, ε)` to the right of `0`.
* `𝓝[≠] 0` is short for `𝓝[{0}ᶜ] 0`: the points near `0` that are *not equal*
  to `0`, i.e. a small interval around `0` with `0` itself removed.
-/
DefinitionDoc nhdsWithin as "𝓝[s]"

NewDefinition Set.Ioi Set.Iio nhdsWithin
