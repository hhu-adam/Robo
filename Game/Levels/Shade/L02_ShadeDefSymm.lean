import Game.Levels.Shade.L01_ShadeDef

World "Shade"
Level 2

Title ""

Introduction "Intro Shade L02: the other direction.

The previous level said that failing to be sunny is the same as lying in the shade.  The mirror
statement is just as useful: failing to lie in the shade is the same as being sunny.  It is proved
the same way — unfold both sets and let `simp` move the negation across the `∃`.
"

open Set FullGrind

/-- A point fails to lie in the shade exactly when it is a sunny point. -/
TheoremDoc not_mem_Shade_iff_mem_Sun as "not_mem_Shade_iff_mem_Sun" in "Shade"

Statement not_mem_Shade_iff_mem_Sun (f : ℝ → ℝ) (a : ℝ) : a ∉ Shade f ↔ a ∈ Sun f := by
  Hint "Same recipe as last time: `simp [Shade, Sun]`. This time the negation has to pass
  through an `∃`."
  simp_log [Shade, Sun]

attribute [game_simp] not_mem_Shade_iff_mem_Sun

Conclusion "Conclusion Shade L02: saved as `not_mem_Shade_iff_mem_Sun`."

TheoremTab "Shade"
