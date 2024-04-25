import Game.Metadata
import Game.Levels.Cantor.L07_fixedPoints_Cantor

World "Cantor"
Level 8

Title "Cantor"

Introduction
"
**Cantor**:
"

open Function Set

Statement cantor_diagonal (f : A → Set A) (hsurj : Surjective f) :
    ∀ (s : Prop → Prop), ∃ x, IsFixedPt s x := by
  intro s
  let G : Set A := fun (a : A) ↦ s (a ∈ f a)
  rcases hsurj G with ⟨a, ha⟩
  use (f a a)
  apply cantor_diagonal_isFixedPt G s
  simp
  assumption


-- theorem cantor_diagonal' (f : A → A → Y) (hsurj : Surjective f) :
--     ∀ (s : Y → Y), Nonempty (fixedPoints s) :=
--   by
--     intro s
--     let g : A → Y := fun (a : A) ↦ s (f a a)   --s ∘ f ∘ (δ A)
--     obtain ⟨a, ha⟩ := hsurj g
--     have : g a = s (f a a) := by rfl
--     use (f a a)
--     rw [mem_fixedPoints_iff]
--     rw [← this]
--     symm
--     apply congr_fun ha
--     -- rw [ha]
