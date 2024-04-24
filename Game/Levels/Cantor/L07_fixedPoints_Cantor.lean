import Game.Metadata

World "Cantor"
Level 6

Title "Cantor"

Introduction
"


"

open Function Set


theorem cantor_diagonal (f : A → A → Y) (hsurj : Surjective f) :
    ∀ (s : Y → Y), ∃ x, IsFixedPt s x :=
  by
    intro s
    let g : A → Y := fun (a : A) ↦ s (f a a)
    obtain ⟨a, ha⟩ := hsurj g
    have : g a = s (f a a) := by rfl
    use (f a a)
    dsimp [IsFixedPt]
    simp [← this]
    symm
    Branch
      apply congr_fun ha
    rw [ha]



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
