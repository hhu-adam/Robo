import Game.Levels.Rigi.L07_ValLeValSSupShaders

World "Rigi"
Level 8

Title ""

Introduction "Intro Rigi L08: past the supremum the value drops back."

open Set

/-- If `b` lies in the shade and `Shaders f b` is bounded above, then every point strictly to the right of `sSup (Shaders f b)` has value at most `f b`. -/
TheoremDoc val_le_of_sSup_Shaders_lt as "val_le_of_sSup_Shaders_lt" in "Shade"

Statement val_le_of_sSup_Shaders_lt (preamble := grind_mode 1) {f : ℝ → ℝ} {b t : ℝ}
    (hb : b ∈ Shade f) (hs : BddAbove (Shaders f b)) (ht : sSup (Shaders f b) < t) :
    f t ≤ f b := by
  Hint (strict := true)
  "[Hint z5c1p] Consider a point `b` in the shade, and a point `t` to the right of the supremum of the shaders of b.
  Start by establishing that t is not a shader of b."
  have not_mem : t ∉ Shaders f b := by
    Hint (hidden := true) "[Hint 5yybw] Try a proof by contradiction."
    by_contra
    Hint (hidden := true) "[Hint ingz4] Remember `le_csSup`."
    have := le_csSup hs this
    grind
  Hint (strict := true) "[Hint 2u5ee] You will also need `lt_sSup_Shaders hb hs`."
  have c_lt := lt_sSup_Shaders hb hs
  unfold Shaders at not_mem
  grind

Conclusion "Conclusion Rigi L08: saved as `val_le_of_sSup_Shaders_lt`."

TheoremTab "Shade"
