import Game.Metadata

open Finset

World "Babylon"
Level 2

Title ""

/-
Introduction "Ihr schaut euch zusammen den nächsten Turm an."
-/
Introduction "`INTRO` Intro Babylon L02"

Statement (I : Finset ℕ) : ∑ i ∈ I, 2 = 2 * card I := by
  /-
  Hint (hidden := true) "**Du**:  Wieder `simp`?"
  -/
  Hint (hidden := true) "Again try using `simp`"
  simp
  ring
