import Game.Metadata

World "Cantor"
Level 5

Title "Image of fixed points"

Introduction
"
The image of a subset `S` of `A` along a function `f : A → B` is the set of
all elements `b : B` such that there exists an element `a ∈ S` with `f a = b`.
In Lean, the image `S` along `f` is defined by `Set.image f S`, and denoted by `f '' S`.

In this level, we will prove that the set of fixed points of a function `f : X → X` is closed
under the operation of taking the image of `f`.

"

open Function Set

Statement (f : X → X) : f '' (fixedPoints f)  ⊆ fixedPoints f := by
  intro y ⟨x, h⟩
  rw [← h.2]
  apply IsFixedPt.apply
  exact h.1
