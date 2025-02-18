import Game.Metadata


World "Mono"
Level 9

Title "Functions with left inverses are injective."

Introduction
"
  In this level you show that a function which has a left inverse is injective.
"

open Function

/---/
TheoremDoc Function.HasLeftInverse.injective as "HasLeftInverse.injective" in "Function"

-- Theorem in Mathlib uses the Definition HasLeftInverse, which we've removed from the game for simplicity.

Statement Function.HasLeftInverse.injective {A B : Type} {f : A → B} (h : ∃ g, LeftInverse g f) :
    Injective f := by
  intro a a' ha
  obtain ⟨g, hg⟩ := h
  Branch
    trans g (f a)
    · rw [hg]
    · rw [ha]
      rw [hg]
  apply congr_arg g at ha
  unfold LeftInverse at hg
  rw [hg a, hg a'] at ha
  assumption
