import Game.Metadata

World "Piazza"
Level 12

Title ""

/-
Introduction "
  **Fin**:  Richtig.   Und jetzt lege ich meine Pistazie wieder zurück.
"
-/
Introduction "`INTRO` Intro Piazza L12"

open Set

Statement (A : Finset ℕ) (a : ℕ) :  insert a A = A ∪ {a} := by
  ext
  simp

TheoremTab "Set"

Conclusion ""
