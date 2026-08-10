import Game.Metadata

World "Hamel"
Level 4

open Finsupp

Introduction "Intro Hamel L04"

/- This level introduces `equivFunOnFinite`. -/

Statement : (equivFunOnFinite.symm ![1, (2 : ℝ)]) 0 = ![1, 2] 0 := by
  Hint "[hml4] On a finite index type `α`, every function is finitely supported, so the two ways of writing
    down a family of coefficients agree. `equivFunOnFinite` is this identification:
    ```
    equivFunOnFinite : (α →₀ M) ≃ (α → M)
    ```"
  Hint (hidden := true) "[hml4h] `simp` can close this goal."
  simp

NewDefinition Finsupp.equivFunOnFinite

TheoremTab "LinearAlgebra"
