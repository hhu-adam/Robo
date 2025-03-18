import Game.Metadata

World "Piazza"
Level 12

Title ""

Introduction "
  **Fin**:  Richtig.   Und jetzt lege ich meine Pistazie wieder zurück.
"

open Set

Statement (A : Finset ℕ) (a : ℕ) :  insert a A = A ∪ {a} := by
  ext
  simp
  tauto

TheoremTab "Set"

Conclusion ""
