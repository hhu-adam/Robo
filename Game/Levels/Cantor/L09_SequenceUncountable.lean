import Game.Metadata

World "Cantor"
Level 9

Title "Cantor"

Introduction
"
In this level you show that no sequence can exhaust `ℕ → ℕ`.
"

open Set Function

Statement (f : ℕ → ℕ → ℕ) : ∃ (g : ℕ → ℕ), ∀ (n : ℕ), g ≠ f n := by

  sorry
