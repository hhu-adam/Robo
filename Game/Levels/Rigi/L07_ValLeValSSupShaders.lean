import Game.Levels.Rigi.L06_LtSSupShaders

World "Rigi"
Level 7

Title ""

Introduction "Intro Rigi L07: the value at the supremum stays up."

open Set

/-- If `f` is continuous, `b` lies in the shade and `Shaders f b` is bounded above, then
`f b ≤ f (sSup (Shaders f b))`. -/
TheoremDoc val_le_val_sSup_Shaders as "val_le_val_sSup_Shaders" in "Shade"

Statement val_le_val_sSup_Shaders (preamble := grind_mode 1) {f : ℝ → ℝ} {hf : Continuous f} {b : ℝ}
    (hb : b ∈ Shade f) (hs : BddAbove (Shaders f b)) :
    f b ≤ f (sSup (Shaders f b)) := by
  Hint (strict := true) "[Hint q8m2v] At the supremum of all shaders of `b`, the mountain is at least as high as at b.
  The proof combines `closure_minimal`, `isClosed_le` and `csSup_mem_closure`.
  Begin by showing that:
  ```
  Shaders f b ⊆ \{t | f b ≤ f t}
  ```
  "
  have h_sub : Shaders f b ⊆ {t | f b ≤ f t} := by
    unfold Shaders
    grind
  Hint (hidden := true) (strict := true)
  "[Hint 9al6z] `closure_minimal` upgrades `{h_sub}` to a statement about the closure."
  apply closure_minimal h_sub
  Hint (hidden := true) (strict := true) "[Hint k3t9w] Two goals are left: the set `\{t | f b ≤ f t}` is closed,
    and the supremum lies in the closure of `Shaders f b`."
  · Hint (hidden := true) "[Hint isclle] That set is closed by `isClosed_le`"
    apply isClosed_le
    Hint (hidden := true) "[Hint r7n4x] Remember `fun_prop`"
    · fun_prop
    · fun_prop
  · apply csSup_mem_closure
    · apply shaders_nonempty
      assumption
    · assumption

Conclusion "Conclusion Rigi L07: saved as `val_le_val_sSup_Shaders`."

TheoremTab "Shade"
