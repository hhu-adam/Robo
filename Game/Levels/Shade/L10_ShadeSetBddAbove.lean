import Game.Levels.Shade.L09_ShadeSetNonempty

World "Shade"
Level 10

Title "Bounded Above"

Introduction "Intro Shade L10: a quick boundedness fact.

To take the supremum `sSup (Shaders f c)`, we also need the set to be bounded above.  This is
immediate: every element of `Shaders f c` lies in `Ioo c b`, hence is below `b`.
"

open Set FullGrind

/-- If `b` lies in the sun, with value `f b < f c`, then `b` bounds `Shaders f c` from above.
-/
TheoremDoc upperBounds_Shaders as "shaders_bddAbove" in "Shade"

Statement upperBounds_Shaders {f : ℝ → ℝ} {c b : ℝ} (h_b_sun : b ∈ Sun f) (h_b_val : f b < f c) :
    b ∈ upperBounds (Shaders f c) := by
  Hint "[Hint bbdshadeh] `b ∈ upperBounds (Shaders f c)` means that `b` is a concrete upper bound of
    `Shaders f c`.  So the claim is:  `∀ y ∈ Shaders f c, y ≤ b`."
  intro y hy
  Hint "[Hint ufgrind] Now best distinguish the three cases `y ≤ b`, `y = b`,
  `b ≤ y`"
  Hint (hidden := true) "[Hint xpkm] Remember `lt_trichotomy`"
  obtain h | h | h := lt_trichotomy y b
  · grind
  · grind
  · have : b ∈ Shade f
    · use y
      simp [Shade] at h_b_sun
      simp [Shaders] at hy
      grind
    rw [mem_Shade_iff_not_mem_Sun] at this
    contradiction


-- ADDITIONAL PREBOSS LEVEL

lemma lt_sSup_Shaders {f : ℝ → ℝ} {c : ℝ} (hc : c ∈ Shade f) (hs : BddAbove (Shaders f c)) :
    c < sSup (Shaders f c) := by
  have h_ne : (Shaders f c).Nonempty := by
    apply shaders_nonempty
    assumption
  obtain ⟨x, hx⟩ := h_ne
  have : x ≤ sSup (Shaders f c) := by
    apply le_csSup
    · assumption
    · assumption
  unfold Shaders at hx
  grind

-- ADDITIONAL PREBOSS LEVEL

lemma val_le_val_sSup_Shaders {f : ℝ → ℝ} {hf : Continuous f} {c : ℝ} (hc : c ∈ Shade f)
    (hs : BddAbove (Shaders f c)) :
    f c ≤ f (sSup (Shaders f c)) := by
  have h_sub : (Shaders f c) ⊆ {x | f c ≤ f x} := by
    unfold Shaders
    grind
  apply closure_minimal h_sub
  have := lt_sSup_Shaders hc hs
  · apply isClosed_le
    · fun_prop
    · fun_prop
  apply csSup_mem_closure
  · apply shaders_nonempty
    assumption
  · assumption

Conclusion "Conclusion Shade L10: saved as `upperBounds_Shaders`."


TheoremTab "Shade"
