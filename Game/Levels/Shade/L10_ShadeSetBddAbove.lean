import Game.Levels.Shade.L09_ShadeSetNonempty

World "Shade"
Level 10

Title "Bounded Above"

Introduction "Intro Shade L10: a quick boundedness fact.

To take the supremum `sSup (shadeSet f c b)`, we also need the set to be bounded above.  This is
immediate: every element of `shadeSet f c b` lies in `Ioo c b`, hence is below `b`.
"

open Set FullGrind

/-- The set `Shaders f c` is bounded above if …. -/
TheoremDoc shaders_bddAbove as "shaders_bddAbove" in "Shade"

Statement shaders_bddAbove {f : ℝ → ℝ} {c b : ℝ} (h_b_sun : b ∉ Shade f) (h_b_val : f b < f c): b ∈ upperBounds (Shaders f c) := by
  Hint "[Hint bbdshadeh] Remember that `shadeSet f c b` is defined as the set of `t ∈ Set.Ioo c b` with `f c ≤ f t`. Therefore,
  `b` is a upperbound of this set. "
  --use b
  intro y hy
  Hint (hidden := true) "[Hint ufgrind] Now just unfold the definition `shadeSet` and use `grind` to closed it. "
  --unfold shadeSet at hy
  obtain h | h | h := lt_trichotomy y b
  · grind (ematch := 0)
  · grind (ematch := 0)
  · have : b ∈ Shade f
    · use y
      simp [Shade] at h_b_sun
      simp [Shaders] at hy
      grind (ematch := 0)
    contradiction


Conclusion "Conclusion Shade L10: saved as `shadeSet_bddAbove`."


TheoremTab "Shade"
