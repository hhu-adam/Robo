import Game.Metadata


World "Epo"
Level 4

Title "Right inverse"

Introduction
"

"

open Function

-- in Mathlib: `Function.rightInverse_iff_comp`
Statement {A B : Type} {f : A -> B} {g : B -> A} :
    RightInverse g f ↔ f ∘ g = id := by
  constructor
  · intro h
    funext x
    Branch
      rw [comp_apply]
      rw [h x]
      rw [id_eq]
    apply h
  · Branch
      apply congr_fun
      done
    intro h
    intro x
    -- TODO: Insert a Hint here about rw [← comp_apply] not working as expected.
    Branch
      rw [← comp_apply (f:= f)]
      rw [h]
      rfl
    Branch
      apply congr_fun at h
      apply h
    apply congr_fun at h
    apply h

TheoremTab "Function"
