import Game.Metadata

World "Espresso"
Level 8

Title ""

open Set Filter Topology FullGrind

Introduction "Intro Espresso L08"

Statement : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] 0 := by
  Hint "[Hint nhdsmno] We have two modified neighborhood filters of `0`.
  `𝓝[>] 0` is the filter “approaching zero from the right”:
  it consists of all sets that contain the positive part of a neighborhood of 0,
  i.e. that contain the intersection of a neighborhood of 0 with $(0,\\infty)$.
  `𝓝[≠] 0` is the filter “approaching zero without ever being equal to zero”:
  it consists of all sets that contain a punctured neighborhood of zero,
  i.e. that contain the intersection of a neighborhood of 0 with $\\mathbb\{R}\\setminus \\\{0\\}$.
  `≤` means that the first filter is finer than the second,
  i.e. that every set in the second is also contained in the first.
  Apply the new theorem `nhdsWithin_mono`."
  apply nhdsWithin_mono
  Hint "[Hint ggfkp] This looks better.
  `Ioi 0` is the interval $(0,∞)$.
  And `\{0}ᶜ` is the complement of `0` in ℝ."
  Hint (hidden := true) "[Hint tg8nh] Try `grind`."
  grind

Conclusion "Conclusion Espresso L08: Remember `grind`."

/---/
TheoremDoc nhdsWithin_mono as "nhdsWithin_mono" in "Topology"

NewTheorem nhdsWithin_mono

NewDefinition Set.Ioi Set.Iio nhdsWithin
