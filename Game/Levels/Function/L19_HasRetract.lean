import Game.Metadata

World "Function2"
Level 19

Title "Functions with left inverses are injective."


Introduction
"
  In this level you show that a function which has a left inverse is injective.
"

open Function

Statement HasLeftInverse.injective {f : α → β} (h : HasLeftInverse f) :
    Injective f := by
  obtain ⟨finv, inv⟩ := h
  intro a b eq
  trans finv (f a)
  · rw [inv]
  · rw [eq]
    rw [inv]
