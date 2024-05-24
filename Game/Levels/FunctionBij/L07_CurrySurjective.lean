import Game.Metadata


World "FunctionBij"
Level 7

Title "Not exhausted by naturals."

Introduction
"

"

open Function Nat

Statement (f : ℕ → A → B) : ¬ Surjective f ↔ ∃ g : A → B, ∀ n, g ≠ f n := by
  constructor
  · intro h
    simp [Surjective] at h
    push_neg at h
    rcases h with ⟨w, hw⟩
    use w
    intro n
    rw [ne_comm]
    apply hw
  · intro ⟨g, hg⟩
    intro hf
    rcases hf g with ⟨n, hn⟩
    apply hg n
    symm
    assumption

NewTheorem ne_comm
