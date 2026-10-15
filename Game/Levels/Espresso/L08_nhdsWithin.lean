import Game.Metadata

World "Espresso"
Level 8

Title ""

open Set Filter Topology FullGrind

Statement : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] 0 := by
  Hint "[Hint nhdsmno] We have two modified neighborhood filters of `0`.
  `𝓝[>] 0` is the filter “approaching zero from the left”:
  it consists of all sets that contain the positive part of a neighborhood of 0.
  `𝓝[≠] 0` is the filter “approaching zero without ever being equal to zero”:
  sets in this filter a given by neighborhoods of zero with zero itself removed.
  The first filter is finer than the second – which means that every sets in the second
  is also contain in the first.
  Apply the new theorem `nhdsWithin_mono`."
  apply nhdsWithin_mono
  Hint "[Hint ggfkp] This looks better.
  `Ioi 0` is the interval $(0,∞)$.
  And `\{0}ᶜ` is the complement of `0` in ℝ.
  The theorem `nhdsWithin_mono` reduced the statement about neighborhoods to this
  elementary statement about sets."
  Hint (hidden := true) "[Hint tg8nh] Try `grind`. "
  grind

Conclusion "Conclusion Espresso L08"

/---/
TheoremDoc nhdsWithin_mono as "nhdsWithin_mono" in "Topology"

NewTheorem nhdsWithin_mono

NewDefinition Set.Ioi Set.Iio nhdsWithin
