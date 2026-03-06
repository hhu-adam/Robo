import Game.Metadata

World "Luna"
Level 8

Title ""

/-
Introduction "
**Ritha**:  Jetzt ich wieder!
"
-/
Introduction "Intro Luna L08"

open Finset
Statement (n x : ℕ) (h : 3 ≤ n): x ∈ Icc 0 n \ Icc 3 n → x = 0 ∨ x = 1 ∨ x = 2 := by
  intro h'
  -- Hint (hidden := true) "**Ritha**:  Probier unbedingt mal `simp at {h'}`."
  Hint (hidden := true) "Definitely use `simp at {h'}`"
  simp at h'
  omega

Conclusion ""
