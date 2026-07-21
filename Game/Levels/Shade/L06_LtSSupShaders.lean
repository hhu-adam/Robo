import Game.Levels.Shade.L05_ShadeSetBddAbove

World "Shade"
Level 6

Title "Above the Starting Point"

Introduction "Intro Shade L06: the supremum lies strictly to the right of `c`.

Now that `Shaders f c` is nonempty and bounded above, its supremum `sSup (Shaders f c)` exists.
The first thing to know about it is that it sits strictly to the right of `c`.

The reason is short: pick any element `x` of `Shaders f c`.  By definition `c < x`, and `x` is
below the supremum, so `c < sSup (Shaders f c)`.
"

open Set FullGrind

/-- If `c` lies in the shade and `Shaders f c` is bounded above, then `c < sSup (Shaders f c)`. -/
TheoremDoc lt_sSup_Shaders as "lt_sSup_Shaders" in "Shade"

Statement lt_sSup_Shaders {f : ℝ → ℝ} {c : ℝ} (hc : c ∈ Shade f) (hs : BddAbove (Shaders f c)) :
    c < sSup (Shaders f c) := by
  Hint "First get hold of an element of the set: it is nonempty by `shaders_nonempty`."
  have h_ne : (Shaders f c).Nonempty := by
    apply shaders_nonempty
    assumption
  obtain ⟨x, hx⟩ := h_ne
  Hint "This `x` is below the supremum. That is `le_csSup`, which wants nonemptiness of the
  bound set and membership of `x`."
  have : x ≤ sSup (Shaders f c) := by
    apply le_csSup
    · assumption
    · assumption
  Hint (hidden := true) "[Hint ltssup] Unfold `Shaders` in `hx` to see `c < x`, then chain the
  two inequalities."
  unfold Shaders at hx
  grind

Conclusion "Conclusion Shade L06: saved as `lt_sSup_Shaders`."

TheoremTab "Shade"
