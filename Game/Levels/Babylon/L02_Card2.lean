import Game.Metadata

open Finset

World "Babylon"
Level 2

Title ""

/-
Introduction "Ihr schaut euch zusammen den nächsten Turm an."
-/
Introduction "Intro Babylon L02"
-- attribute [game_simp] sum_const smul_eq_mul

Statement (I : Finset ℕ) : ∑ i ∈ I, 2 = 2 * card I := by
  /-
  Hint (hidden := true) "**Du**:  Wieder `simp`?"
  -/
  Hint (hidden := true) "Again try using `simp`"
  simp
  ring
