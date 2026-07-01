import Game.Levels.Shade.L08_ShadeDef

World "Shade"
Level 9

Title "The Set Below the Sup"

Introduction "Intro Shade L09: introduce the working set.

Fix two points `c` and `b`.  We study the set of points strictly between `c` and `b` at which `f`
rises above `f c`:

```
shadeSet f c b := {t ∈ Ioo c b | f c < f t}
```

Later we take the supremum of this set.  For that we first need it to be nonempty.  Assuming `b` is
not a shadow point, `f b < f c`, and `c` itself is a shadow point, you show the set is nonempty.
"

open Set FullGrind

def shadeSet (f : ℝ → ℝ) (c b : ℝ) : Set ℝ := {t ∈ Set.Ioo c b | f c ≤ f t}

/-- `shadeSet f c b` is the set of `t` strictly between `c` and `b` with `f c < f t`. -/
DefinitionDoc shadeSet as "shadeSet" in "Shade"

/-- If `b` is not a shadow point, `f b < f c`, and `c` is a shadow point, then `shadeSet f c b`
is nonempty. -/
TheoremDoc shadeSet_nonempty as "shadeSet_nonempty" in "Shade"

Statement shadeSet_nonempty {f : ℝ → ℝ} {b c : ℝ} (hb : b ∉ Shade f)
    (hbc : f b < f c) (hc_shade : c ∈ Shade f) : (shadeSet f c b).Nonempty := by
  Hint "Because `c` is a shadow point, there is some `t₀ > c` with `f t₀ > f c`. Unpack it with
  `obtain ⟨t₀, ht₀_gt, ht₀_f⟩ := hc_shade`."
  obtain ⟨t₀, ht₀_gt, ht₀_f⟩ := hc_shade
  Hint "The only thing left to check is that this `t₀` lies below `b`. Compare `t₀` with `b` by
  trichotomy; the cases `t₀ = b` and `t₀ > b` both contradict the hypotheses."
  have ht₀_lt : t₀ < b := by
    obtain hlt | heq | hgt := lt_trichotomy t₀ b
    · assumption
    · grind
    · by_contra
      have : b ∈ Shade f := by
        use t₀
        grind
      contradiction
  use t₀
  unfold shadeSet
  grind

Conclusion "Conclusion Shade L09: saved as `shadeSet_nonempty`."

NewDefinition shadeSet

TheoremTab "Shade"
