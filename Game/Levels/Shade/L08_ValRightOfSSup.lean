import Game.Levels.Shade.L07_ValLeValSSupShaders

World "Shade"
Level 8

Title ""

Introduction "Intro Shade L08: past the supremum the value drops back.

Write `s := sSup (Shaders f b)`.  Any point `t` strictly to the right of `s` cannot belong to
`Shaders f b`.  By the definition of `Shaders f b `, a point `t > b`
fails to be in the set precisely when `f t < f b`.  Combining these gives `f t ≤ f b` for every
`t > s`.

The key new tool is `notMem_of_csSup_lt`: if `sSup s < t` and `s` is bounded above, then `t ∉ s`.
"

open Set FullGrind

/-- If `b` lies in the shade and `Shaders f b` is bounded above, then every point strictly to the
right of `sSup (Shaders f b)` has value at most `f b`. -/
TheoremDoc val_le_of_sSup_Shaders_lt as "val_le_of_sSup_Shaders_lt" in "Shade"

Statement val_le_of_sSup_Shaders_lt {f : ℝ → ℝ} {b t : ℝ} (hb : b ∈ Shade f)
    (hs : BddAbove (Shaders f b)) (ht : sSup (Shaders f b) < t) :
    f t ≤ f b := by
  Hint "[Hint eymq5] Establish `t ∉ Shaders f b` with `have`."
  have not_mem : t ∉ Shaders f b := by
    Hint (hidden := true) "Since `t` lies above the supremum, it is not in the set.
      Use `notMem_of_csSup_lt`"
    apply notMem_of_csSup_lt
    · assumption
    · assumption
  Hint (strict := true) "[Hint 2u5ee] You will also need `b < t`."
  have c_lt : b < sSup (Shaders f b) := by
    Hint (hidden := true) "[Hint ux181] Remember `lt_sSup_Shaders`."
    apply lt_sSup_Shaders hb hs
  Hint (hidden := true) "[Hint vrsup] Unfold `Shaders` in `{not_mem}`, then `grind` closes it."
  unfold Shaders at not_mem
  grind

Conclusion "Conclusion Shade L08: saved as `val_le_of_sSup_Shaders_lt`."

/-- If `sSup s < x` and `s` is bounded above, then `x ∉ s`. -/
TheoremDoc notMem_of_csSup_lt as "notMem_of_csSup_lt" in "sSup"

NewTheorem notMem_of_csSup_lt

TheoremTab "Shade"
