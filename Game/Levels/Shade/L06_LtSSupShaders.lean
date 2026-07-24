import Game.Levels.Shade.L05_ShadeSetBddAbove

World "Shade"
Level 6

Title ""

Introduction "Intro Shade L06: the supremum lies strictly to the right of `b`.

Now that `Shaders f b` is nonempty and bounded above, its supremum `sSup (Shaders f b)` exists.
The first thing to know about it is that it sits strictly to the right of `b`.

The reason is short: pick any element `t` of `Shaders f b`.  By definition `b < t`, and `t` is
below the supremum, so `b < sSup (Shaders f b)`.
"

open Set FullGrind

/-- If `b` lies in the shade and `Shaders f b` is bounded above, then `b < sSup (Shaders f b)`. -/
TheoremDoc lt_sSup_Shaders as "lt_sSup_Shaders" in "Shade"

Statement lt_sSup_Shaders {f : ℝ → ℝ} {b : ℝ} (hb : b ∈ Shade f) (hs : BddAbove (Shaders f b)) :
    b < sSup (Shaders f b) := by
  Hint "First get hold of an element of the set: it is nonempty by `shaders_nonempty`."
  have h_ne : (Shaders f b).Nonempty := by
    apply shaders_nonempty
    assumption
  obtain ⟨t, ht⟩ := h_ne
  Hint "This `{t}` is below the supremum. Remember `le_csSup`."
  have : t ≤ sSup (Shaders f b) := by
    apply le_csSup
    · assumption
    · assumption
  Hint (hidden := true) "[Hint ltssup] Unfold `Shaders` in `{ht}` to see `b < t`."
  unfold Shaders at ht
  grind

Conclusion "Conclusion Shade L06: saved as `lt_sSup_Shaders`."

TheoremTab "Shade"
