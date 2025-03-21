import Game.Metadata

open Finset

World "Babylon"
Level 2

Title ""

Introduction "Ihr schaut euch zusammen den nächsten Turm an."

Statement (I : Finset ℕ) : ∑ i ∈ I, 2 = 2 * card I := by
  Hint (hidden := true) "**Du**:  Wieder `simp`?"
  simp
  ring
