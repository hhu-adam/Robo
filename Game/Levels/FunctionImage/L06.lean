import Game.Metadata

open Function Set

World "FunctionImage"
Level 6

Title "Preimage of surjective is injective"

Introduction
""

-- new level
theorem preimage_not_empty_iff {A B : Type} (f : A → B)  (y : B) :
     f ⁻¹' {y} ≠ ∅ ↔ (∃ a, f a = y) := by
  unfold Ne
  rw [eq_empty_iff_forall_not_mem]
  simp
