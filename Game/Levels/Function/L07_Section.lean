import Game.Metadata

World "Function2"
Level 7

Title "Section"


Introduction
"
A function `g : B → A` is a right inverse of a function `f : A → B` if for all `a : A`, `f (g a) = a`.

In this level, you will prove that if `g` is a right inverse of `f`, then the composition `f ∘ g` is the identity function on `B`.

"

open Function

Statement rightInverse_iff_comp {f : A -> B} {g : B -> A} :
    RightInverse g f ↔ f ∘ g = id := by
  constructor
  · intro h
    ext x
    Branch
      rw [comp_apply]
      rw [h x]
      rw [id_eq]
    simp [h x]
  · Branch
      apply congr_fun
    intro h
    intro x
    have h := congr_fun h
    apply h

NewTactic ext congr
NewDefinition Function.RightInverse
NewTheorem Function.rightInverse_iff_comp congr_fun congr_arg
TheoremTab "Function"
