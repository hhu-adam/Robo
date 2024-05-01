import Game.Metadata


World "Function"
Level 27

Title "Not exhausted by naturals."

Introduction
"

"

open Function Nat

Statement (f : ℕ → A → B) : ¬ Surjective f ↔ ∃ g : A → B, ∀ n, g ≠ f n := by
  constructor
  · intro h
    dsimp [Surjective] at h
    push_neg at h
    simpa only [ne_comm] using h
  · intro ⟨g, hg⟩
    intro hf
    obtain ⟨n, hn⟩ :=  hf g
    apply hg n
    exact hn.symm
