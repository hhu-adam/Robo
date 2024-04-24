import Game.Metadata
import Game.Levels.Cantor.L07_fixedPoints_Cantor

World "Cantor"
Level 8

Title "Cantor"

Introduction
"
Use the lemma `cantor_diagonal_fixed_point` from the previous level to
prove the Cantor diagonal theorem.
"

open Function Set


Statement cantor_diagonal (f : A → A → Y) (hsurj : Surjective f) :
    ∀ (s : Y → Y), ∃ x, IsFixedPt s x :=
  by
    intro s
    let g : A → Y := fun (a : A) ↦ s (f a a)
    obtain ⟨a, ha⟩ := hsurj g
    use (f a a)
    apply cantor_diagonal_fixed_point g s
    simp
    assumption



-- theorem cantor_diagonal (f : A → A → Y) (hsurj : Surjective f) :
--     ∀ (s : Y → Y), ∃ x, IsFixedPt s x :=
--   by
--     intro s
--     let g : A → Y := fun (a : A) ↦ s (f a a)
--     obtain ⟨a, ha⟩ := hsurj g
--     have : g a = s (f a a) := by rfl
--     use (f a a)
--     dsimp [IsFixedPt]
--     simp [← this]
--     symm
--     Branch
--       apply congr_fun ha
--     rw [ha]

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
