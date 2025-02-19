import Game.Metadata


World "Mono"
Level 9

Title ""

Introduction ""

open Function

/---/
TheoremDoc Function.HasLeftInverse.injective as "HasLeftInverse.injective" in "Function"

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
