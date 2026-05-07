import Game.Metadata

World "Piazza"
Level 12

Title ""

/-
Introduction "
  **Fin**:  Richtig.   Und jetzt lege ich meine Pistazie wieder zurück.
"
-/
Introduction "Intro Piazza L12"

open Set
-- attribute [game_simp] Finset.mem_insert Finset.union_singleton

Statement (A : Finset ℕ) (a : ℕ) :  insert a A = A ∪ {a} := by
  ext
  simp

TheoremTab "Set"

Conclusion ""
