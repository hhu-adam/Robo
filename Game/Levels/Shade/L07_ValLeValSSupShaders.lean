import Game.Levels.Shade.L06_LtSSupShaders

World "Shade"
Level 7

Title "The Value at the Supremum"

Introduction "Intro Shade L07: the value at the supremum stays up.

Every point of `t ∈ Shaders f b` satisfies `f b ≤ f t`.  The supremum itself need not be a point of
`Shaders f b`, but it lies in its *closure* — and the condition `f b ≤ f t` is a closed condition,
because `f` is continuous.  So the inequality survives the passage to the limit:

```
f b ≤ f (sSup (Shaders f b))
```

The proof combines `closure_minimal`, `isClosed_le` and the `csSup_mem_closure` fact from `Aquarium`.
"

open Set FullGrind

/-- If `f` is continuous, `b` lies in the shade and `Shaders f b` is bounded above, then
`f b ≤ f (sSup (Shaders f b))`. -/
TheoremDoc val_le_val_sSup_Shaders as "val_le_val_sSup_Shaders" in "Shade"

Statement val_le_val_sSup_Shaders {f : ℝ → ℝ} {hf : Continuous f} {b : ℝ} (hb : b ∈ Shade f)
    (hs : BddAbove (Shaders f b)) :
    f b ≤ f (sSup (Shaders f b)) := by
  Hint "State the containment that makes the argument work: `Shaders f b` is contained in the set
    of points `t` where `f b ≤ f t`."
  have h_sub : Shaders f b ⊆ {t | f b ≤ f t} := by
    unfold Shaders
    grind
  Hint "`closure_minimal` upgrades that to a statement about the closure — it leaves you with
    two goals: the right-hand set is closed, and the supremum lies in the closure."
  apply closure_minimal h_sub
  have := lt_sSup_Shaders hb hs
  · Hint (hidden := true) "[Hint isclle] That set is closed by `isClosed_le`"
    apply isClosed_le
    Hint (hidden := true) "[Hint 7xd8e] Remember `fun_prop`"
    · fun_prop
    · fun_prop
  Hint (hidden := true) (strict := true ) "[Hint csmc] The remaining goal is exactly
    `csSup_mem_closure`."
  apply csSup_mem_closure
  · apply shaders_nonempty
    assumption
  · assumption

Conclusion "Conclusion Shade L07: saved as `val_le_val_sSup_Shaders`."

TheoremTab "Shade"
