import Game.Levels.Shade.L01_ShadeDef

World "Shade"
Level 2

Title "The Set Below the Sup"

Introduction "Intro Shade L09: introduce the working set.

Fix two points `c` and `b`.  We study the set of points strictly between `c` and `b` at which `f`
rises above `f c`:

```
Shaders f c := {t ∈ Set.Ioi c | f c ≤ f t}
```

Later we take the supremum of this set.  For that we first need it to be nonempty.  Assuming `b` is
not a shadow point, `f b < f c`, and `c` itself is a shadow point, you show the set is nonempty.
"

open Set FullGrind

def Shaders (f : ℝ → ℝ) (c : ℝ) : Set ℝ := {t ∈ Set.Ioi c | f c ≤ f t}

lemma lt_Shader (f : ℝ → ℝ) (c : ℝ) (s : ℝ) (hs : s ∈ Shaders f c) : c < s := by
  unfold Shaders at hs
  simp_log at hs
  grind

/-- `Shaders f c` is the set of `t` strictly larger than `c` such that `f c < f t`. -/
DefinitionDoc Shaders as "Shaders" in "Shade"

/-- If `b` is not a shadow point, `f b < f c`, and `c` is a shadow point, then `Shaders f c`
is nonempty. -/
TheoremDoc shaders_nonempty as "shaders_nonempty" in "Shade"

Statement shaders_nonempty {f : ℝ → ℝ} {c : ℝ}
    (hc_shade : c ∈ Shade f) : (Shaders f c).Nonempty := by
  Hint "Because `c` is a shadow point, there is some `t₀ > c` with `f t₀ > f c`. Unpack it with
  `obtain ⟨t₀, ht₀_gt, ht₀_f⟩ := hc_shade`."
  obtain ⟨t₀, ht₀_gt, ht₀_f⟩ := hc_shade
  Hint "The only thing left to check is that this `t₀` lies below `b`. Compare `t₀` with `b` by
  trichotomy; the cases `t₀ = b` and `t₀ > b` both contradict the hypotheses."
  use t₀
  unfold Shaders
  grind




Conclusion "Conclusion Shade L09: saved as `shaders_nonempty`."

NewDefinition Shaders

TheoremTab "Shade"
