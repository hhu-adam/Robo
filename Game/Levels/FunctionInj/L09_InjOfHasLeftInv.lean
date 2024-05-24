import Game.Metadata


World "FunctionInj"
Level 9

Title "Functions with left inverses are injective."

Introduction
"
  In this level you show that a function which has a left inverse is injective.
"

open Function

Statement HasLeftInverse.injective {f : α → β} (h : HasLeftInverse f) :
    Injective f := by
  rcases h with ⟨finv, inv⟩
  intro a b eq
  trans finv (f a)
  · rw [inv]
  · rw [eq]
    rw [inv]

NewTactic trans
