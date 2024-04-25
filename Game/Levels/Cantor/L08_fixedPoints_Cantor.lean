import Game.Metadata

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
    apply cantor_diagonal_isFixedPt g s
    simp
    assumption

NewTheorem cantor_diagonal
TheoremTab "Function"
