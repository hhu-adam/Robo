import Game.Metadata

World "Cantor"
Level 5

Title "Image of fixed points"

-- Maybe we don't need this level.
-- At least this year they also don't know about `Function.image` yet.

Introduction
"

"

open Function Set

Statement (f : X → X) : f '' (fixedPoints f)  ⊆ fixedPoints f := by
  Branch
    intro y hy
    rcases hy with ⟨x, h₁, h₂⟩
    rw [← h₂]
    apply IsFixedPt.apply
    assumption
  simp
  tauto


-- TODO: Introduce image in Function world
NewTheorem Function.IsFixedPt.apply
TheoremTab "Function"
