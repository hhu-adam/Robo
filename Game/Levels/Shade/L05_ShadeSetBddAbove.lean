import Game.Levels.Shade.L04_ShadeSetNonempty

World "Shade"
Level 5

Title ""

Introduction "Intro Shade L05: a quick boundedness fact.

To take the supremum `sSup (Shaders f b)`, we also need the set to be bounded above.
"

open Set FullGrind

/-- If `c` is a sunny point with `f b < f c`, then `c` bounds `Shaders f b` from above.
-/
TheoremDoc upperBounds_Shaders as "shaders_bddAbove" in "Shade"

Statement upperBounds_Shaders {f : ℝ → ℝ} {b c : ℝ} (hc : c ∈ Sun f) (hfc : f c < f b) :
    c ∈ upperBounds (Shaders f b) := by
  Hint "[Hint bbdshadeh] `c ∈ upperBounds (Shaders f b)` means that `c` is a concrete upper bound of
    `Shaders f b`.  So the claim is:  `∀ t ∈ Shaders f b, t ≤ b`."
  intro t ht
  Hint "[Hint ufgrind] Now best distinguish the three cases `t < c`, `t = c`,`c < t`"
  Hint (hidden := true) "[Hint xpkm] Remember `lt_trichotomy`"
  obtain h | h | h := lt_trichotomy t c
  · grind
  · grind
  · have : c ∈ Shade f
    · use t
      simp [Shade] at hc
      simp [Shaders] at ht
      grind
    rw [← not_mem_Sun_iff_mem_Shade] at this
    contradiction

Conclusion "Conclusion Shade L05: saved as `upperBounds_Shaders`."


TheoremTab "Shade"
