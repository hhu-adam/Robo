import Mathlib


open BigOperators Finset

example (f : Fin n → ℕ) (h : ∀ k, f k ≠ 0) (hn : n > 0) :
    ∑ i : Fin n, f i ≠ 0 := by
  rw [← Nat.pos_iff_ne_zero]
  apply Finset.sum_pos (fun k _ ↦ Nat.pos_iff_ne_zero.mpr (h k))
  use ⟨0, hn⟩
  simp only [mem_univ]


example (f : Fin n → ℕ) (h : ∃ k : Fin n, f k ≠ 0) (hn : n > 0) :
    ∑ i : Fin n, f i ≠ 0 := by
  rw [← Nat.pos_iff_ne_zero]
  sorry
