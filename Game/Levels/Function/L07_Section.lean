import Game.Metadata

World "Function"
Level 7

Title "Section"


Introduction
"
A function `g : B → A` is a right inverse of a function `f : A → B` if for all `a : A`, `f (g a) = a`.

In this level, you will prove that if `g` is a right inverse of `f`, then the composition `f ∘ g` is the identity function on `B`.

"

open Function

Statement RightInverse.comp_eq_id {f : A -> B} {g : B -> A} :
    RightInverse g f ↔ f ∘ g = id := by
  constructor
  · intro h
    funext x
    Branch
      rw [comp_apply]
      rw [h x]
      rw [id_eq]
    simp [h x]
  · Branch
      apply congr_fun
    intro h
    intro x
    exact congr_fun h x
