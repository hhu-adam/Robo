import Game.Levels.Rigi.L01_ShadeDef

World "Rigi"
Level 2

Title ""


Introduction "Intro Rigi L02: the other direction.

The previous level said that failing to be sunny is the same as lying in the shade.  The mirror
statement is just as useful: failing to lie in the shade is the same as being sunny.  It is proved
the same way — unfold both sets and let `simp` move the negation across the `∃`.
"

open Set

/-- A point fails to lie in the shade exactly when it is a sunny point. -/
TheoremDoc not_mem_Shade_iff_mem_Sun as "not_mem_Shade_iff_mem_Sun" in "Shade"

Statement not_mem_Shade_iff_mem_Sun (preamble := grind_mode 1) (f : ℝ → ℝ) (a : ℝ) : a ∉ Shade f ↔ a ∈ Sun f := by
  simp [Shade, Sun]

attribute [game_simp] not_mem_Shade_iff_mem_Sun

Conclusion "Conclusion Rigi L02: saved as `not_mem_Shade_iff_mem_Sun`."

TheoremTab "Shade"
