import Game.Metadata

World "Cantor"
Level 7

Title "Cantor"

Introduction
"



$$
  $$
  \\begin{CD}
       A  @>{f}>> B @<{g}<< C    \\\\
    @V{h}VV    @V{i}VV   @V{j}VV \\\\
       D  @<{k}<< E @>{l}>> F    \\\\
    @A{m}AA    @A{n}AA   @V{p}VV \\\\
       G  @<{q}<< H @>{r}>> I
  \\end{CD}
  $$
$$

"

open Function Set

Statement cantor_diagonal (f : A → A → Y) (hsurj : Surjective f) :
    ∀ (s : Y → Y), ∃ x, IsFixedPt s x := by
  intro s
  Branch

lemma cantor_diagonal_fixed_point {f : A → A → Y} (g : A → Y) (s : Y → Y)
(h₁ : ∀ x, g x = s (f x x)) (a : A) (h₂ : f a = g) : IsFixedPt s (f a a) :=
  by
    dsimp [IsFixedPt]
    rw [← h₂] at h₁
    symm
    exact h₁ a

theorem cantor_diagonal' (f : A → A → Y) (hsurj : Surjective f) :
    ∀ (s : Y → Y), ∃ x, IsFixedPt s x :=
  by
    intro s
    let g : A → Y := fun (a : A) ↦ s (f a a)
    obtain ⟨a, ha⟩ := hsurj g
    use (f a a)
    apply cantor_diagonal_fixed_point g s
    simp
    assumption



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

    sorry

  Hint "Versuch `g := fun a ↦ s (f a a)`"
  let g : A → Y := fun (a : A) ↦ s (f a a)   -- s ∘ f ∘ (δ A)
  rcases hsurj g with ⟨a, ha⟩
  have : g a = s (f a a)
  · rfl
  use (f a a)
  unfold IsFixedPt
  simp [← this]
  symm
  Branch
    apply congr_fun ha
  rw [ha]

TheoremTab "Function"

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
