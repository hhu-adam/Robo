import Game.Levels.Shade.L06_LtSSupShaders

World "Shade"
Level 7

Title "The Value at the Supremum"

Introduction "Intro Shade L07: the value at the supremum stays up.

Every point of `Shaders f c` satisfies `f c ≤ f x`.  The supremum itself need not be a point of
`Shaders f c`, but it lies in its *closure* — and the condition `f c ≤ f x` is a closed condition,
because `f` is continuous.  So the inequality survives the passage to the limit:

```
f c ≤ f (sSup (Shaders f c))
```

The proof combines `closure_minimal`, `isClosed_le` and the `csSup_mem_closure` fact from `Culmen`.
"

open Set FullGrind

/-- If `f` is continuous, `c` lies in the shade and `Shaders f c` is bounded above, then
`f c ≤ f (sSup (Shaders f c))`. -/
TheoremDoc val_le_val_sSup_Shaders as "val_le_val_sSup_Shaders" in "Shade"

Statement val_le_val_sSup_Shaders {f : ℝ → ℝ} {hf : Continuous f} {c : ℝ} (hc : c ∈ Shade f)
    (hs : BddAbove (Shaders f c)) :
    f c ≤ f (sSup (Shaders f c)) := by
  Hint "State the containment that makes the argument work: `Shaders f c` is contained in the set
  of points where `f c ≤ f x`."
  have h_sub : (Shaders f c) ⊆ {x | f c ≤ f x} := by
    unfold Shaders
    grind
  Hint "`closure_minimal` upgrades that to a statement about the closure — it leaves you with
  two goals: the right-hand set is closed, and the supremum lies in the closure."
  apply closure_minimal h_sub
  have := lt_sSup_Shaders hc hs
  · Hint (hidden := true) "[Hint isclle] That set is closed by `isClosed_le`; both
    sides are continuous, so `fun_prop` discharges the side goals."
    apply isClosed_le
    · fun_prop
    · fun_prop
  Hint (hidden := true) "[Hint csmc] The remaining goal is exactly `csSup_mem_closure`."
  apply csSup_mem_closure
  · apply shaders_nonempty
    assumption
  · assumption

Conclusion "Conclusion Shade L07: saved as `val_le_val_sSup_Shaders`."

TheoremTab "Shade"
