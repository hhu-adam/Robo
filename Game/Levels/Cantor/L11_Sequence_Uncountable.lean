import Game.Metadata

import Game.Levels.Cantor.L08_fixedPoints_Cantor

World "Cantor"
Level 11

Title "Cantor"

Introduction
"

In this level you show that no sequence can exhaust `ℕ → ℕ`.
"

open Set Function Nat

Statement : ∀ (f : ℕ → ℕ → ℕ), ∃ (g : ℕ → ℕ), ∀ (n : ℕ), f n ≠ g := by
  intro f
  have h : ¬ Surjective f := by
    intro h
    apply cantor_diagonal at h
    specialize h succ
    obtain ⟨n, hn⟩ := h
    dsimp [IsFixedPt] at hn
    simp only [Nat.succ_ne_self] at hn
  unfold Surjective at h
  push_neg at h
  assumption
