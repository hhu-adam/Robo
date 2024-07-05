import Game.Metadata


World "FunctionSurj"
Level 4

Title "Right inverse"


Introduction
"
A function `g : B → A` is a right inverse of a function `f : A → B` if for all `b : B`,
`f (g b) = b`.

In this level, you will prove that if `g` is a right inverse of `f`, then the composition `f ∘ g`
equals the identity function on `B`.

"
-- TODO: introduce comp_apply
-- TODO: introduce congr_fun


open Function

Statement rightInverse_iff_comp {A B : Type} {f : A -> B} {g : B -> A} :
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
    -- TODO: Insert a Hint here about rw [← comp_apply] not working as expected.
    -- rw [← comp_apply (f:= f)] works.
    Branch
      apply congr_fun at h
      apply h
    apply congr_fun h

NewTactic congr
NewHiddenTactic funext -- TODO: mention funext in the docs for ext
NewDefinition Function.RightInverse
NewTheorem Function.rightInverse_iff_comp congr_arg congr_fun
TheoremTab "Function"
