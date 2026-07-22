import Game.Levels.Shade.L07_ValLeValSSupShaders

World "Shade"
Level 8

Title "To the Right of the Supremum"

Introduction "Intro Shade L08: past the supremum the value drops back.

Write `d := sSup (Shaders f c)`.  Any point `x` strictly to the right of `d` lies above the
supremum, so it cannot belong to `Shaders f c`.  By the definition of `Shaders`, a point `x > c`
fails to be in the set precisely when `f x < f c`.  Combining these gives `f x ≤ f c` for every
`x > d`.

The key new tool is `notMem_of_csSup_lt`: if `sSup s < x` and `s` is bounded above, then `x ∉ s`.
"

open Set FullGrind

/-- If `c` lies in the shade and `Shaders f c` is bounded above, then every point strictly to the
right of `sSup (Shaders f c)` has value at most `f c`. -/
TheoremDoc val_le_of_sSup_Shaders_lt as "val_le_of_sSup_Shaders_lt" in "Shade"

Statement val_le_of_sSup_Shaders_lt {f : ℝ → ℝ} {c : ℝ} (hc : c ∈ Shade f)
    (hs : BddAbove (Shaders f c)) (x : ℝ) (hx : sSup (Shaders f c) < x) :
    f x ≤ f c := by
  Hint "Since `x` lies above the supremum, it is not in the set. Use `notMem_of_csSup_lt` — it
  wants `sSup (Shaders f c) < x` and `BddAbove (Shaders f c)`."
  have not_mem : x ∉ Shaders f c := by
    apply notMem_of_csSup_lt
    · assumption
    · assumption
  Hint "You will also need `c < x`. That follows because `c < sSup (Shaders f c)` by
  `lt_sSup_Shaders`, and `sSup (Shaders f c) < x`."
  have c_lt : c < sSup (Shaders f c) := lt_sSup_Shaders hc hs
  Hint (hidden := true) "[Hint vrsup] Unfold `Shaders` in `not_mem`, then `grind` closes it."
  unfold Shaders at not_mem
  grind

Conclusion "Conclusion Shade L08: saved as `val_le_of_sSup_Shaders_lt`."

/-- If `sSup s < x` and `s` is bounded above, then `x ∉ s`. -/
TheoremDoc notMem_of_csSup_lt as "notMem_of_csSup_lt" in "sSup"

NewTheorem notMem_of_csSup_lt

TheoremTab "Shade"
