import Game.Metadata


World "Function"
Level 5

Title "Choosing an arbitrary element of a nonempty type."


Introduction
"
"

open Function Set Nat


Statement {A : Type*} [h : Nonempty A] (f : ℕ → A) :
    ∃ g : ℤ → A, ∀ n : ℕ, (f n = g n) := by
  let g : ℤ → A := fun n ↦ if (0 ≤ n) then f (Int.toNat n) else Classical.arbitrary A
  use g
  intro n
  simp [g]

-- TODO: Add as level 7b)
example {A : Type*} [h : Nonempty A] (f : ℕ → A) :
    ∃ g : ℤ → A, ∀ n > 0, (f n = g n) := by
  let g : ℤ → A := fun n ↦ if (0 < n) then f (Int.toNat n) else Classical.arbitrary A
  use g
  intro n hn
  simp [g]
  by_cases h₂ : 0 < n
  · rw [if_pos h₂]
  · rw [if_neg h₂]
    contradiction

NewTheorem Classical.arbitrary
