import Game.Metadata


World "Mono"
Level 9

Title "Functions with left inverses are injective."

Introduction
"
  In this level you show that a function which has a left inverse is injective.
"

open Function

Statement HasLeftInverse.injective {A B : Type} {f : A → B} (h : HasLeftInverse f) :
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
