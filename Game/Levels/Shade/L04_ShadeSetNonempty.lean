import Game.Levels.Shade.L03_MemSun

World "Shade"
Level 4

Title ""

Introduction "Intro Shade L04: introduce the working set.

Fix a point `b`.  We study the set of points to the right of b at which `f`
rises above `f b`:

```
Shaders f b := {t ∈ Set.Ioi b | f b ≤ f t}
```

Later we take the supremum of this set.  For that we first need it to be nonempty.  Assuming b is
not a shadow point, `f b < f c`, and `c` itself is a shadow point, you show the set is nonempty.
"

open Set FullGrind

def Shaders (f : ℝ → ℝ) (c : ℝ) : Set ℝ := {t ∈ Set.Ioi c | f c ≤ f t}

/-- `Shaders f c` is the set of `t` strictly larger than `c` such that `f c < f t`. -/
DefinitionDoc Shaders as "Shaders" in "Shade"

/-- If `b` is not a shadow point, `f b < f c`, and `c` is a shadow point, then `Shaders f c`
is nonempty. -/
TheoremDoc shaders_nonempty as "shaders_nonempty" in "Shade"

Statement shaders_nonempty {f : ℝ → ℝ} {b : ℝ}
    (hb : b ∈ Shade f) : (Shaders f b).Nonempty := by
  Hint "Because `b` is in the shade, there is some `t > b` with `f t > f b`"
  Hint (hidden := true) "[Hint 7xd8e] Unpack `b ∈ Shade f` with `obtain ⟨t, …, …⟩ := hb`."
  obtain ⟨t, _, _⟩ := hb
  Hint (hidden := true) "[Hint eymq5] Now `use` `t`."
  use t
  unfold Shaders
  grind


Conclusion "Conclusion Shade L04: saved as `shaders_nonempty`."

NewDefinition Shaders

TheoremTab "Shade"
