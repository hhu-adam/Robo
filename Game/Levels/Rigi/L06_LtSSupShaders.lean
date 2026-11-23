import Game.Levels.Rigi.L05_ShadeSetBddAbove

World "Rigi"
Level 6

Title ""

Introduction "Intro Rigi L06: the supremum lies strictly to the right of `b`."

open Set

/-- If `b` lies in the shade and `Shaders f b` is bounded above, then `b < sSup (Shaders f b)`. -/
TheoremDoc lt_sSup_Shaders as "lt_sSup_Shaders" in "Shade"

Statement lt_sSup_Shaders (preamble := grind_mode 1) {f : ℝ → ℝ} {b : ℝ} (hb : b ∈ Shade f) (hs : BddAbove (Shaders f b)) :
    b < sSup (Shaders f b) := by
  Hint (strict := true)
  "[Hint wouvk] The supremum of all shaders of `b` is strictly larger than b.
  First, show that there exists some shader.
  This shader will be strictly larger than b by the very definition of `Shaders f b`.
  And the supremum of all shaders will be at least as large as this particular one.
  "
  Hint (strict := true) (hidden := true)
  "[Hint p4nen] First get hold of an element of the set: it is nonempty by `shaders_nonempty`."
  have h_ne := shaders_nonempty hb
  Hint (strict := true) "[Hint 2cfq0] Now you can extract a shader from the hypothesis `{h_ne}`."
  obtain ⟨t, ht⟩ := h_ne
  Hint (hidden := true) "[Hint 59m0w] Remember `le_csSup`."
  have : t ≤ sSup (Shaders f b) := by
    apply le_csSup
    · assumption
    · assumption
  Hint (hidden := true) "[Hint ltssup] Looks good.  Now unfold `Shaders` in `{ht}`."
  unfold Shaders at ht
  grind

Conclusion "Conclusion Rigi L06: saved as `lt_sSup_Shaders`."

TheoremTab "Shade"
