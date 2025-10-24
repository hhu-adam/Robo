import Game.Metadata

World "Piazza"
Level 6

Title "" -- "leere Menge"

/-
Introduction
"
Die leere Menge wird als `(∅ : Set A)` geschrieben.

Hier ein nützliches Lemma.
"
-/
Introduction "Intro Piazza O06"

open Set

Statement Set.eq_empty_iff_forall_not_mem {A : Type} (s : Set A) :
    s = ∅ ↔ ∀ x, x ∉ s := by
  constructor
  · intro h
    rw [h]
    tauto
  · intro h
    ext i
    tauto

/-- -/
DefinitionDoc Set.empty as "∅"

NewDefinition Set.empty
TheoremTab "Set"

Conclusion "Conclusion Piazza O06"
