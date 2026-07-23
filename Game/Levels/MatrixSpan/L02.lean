import Game.Metadata

World "Span"
Level 2

Title "Scaling Distributes"

Introduction "The other rule you will use constantly: scaling **distributes** over vector
addition.  Scaling the sum `x + y` by `a` is the same as scaling each piece and then adding:

`a • (x + y) = a • x + a • y`.

This is `smul_add`.  Together with `two_smul` from the previous level, these are the only module
facts you need to get started.
"

open Real Function Set Finset

/-- `smul_add` : scaling distributes over addition, `a • (x + y) = a • x + a • y`. -/
TheoremDoc smul_add as "smul_add" in "LinearAlgebra"

Statement {V : Type*} [AddCommMonoid V] [Module ℝ V] (a : ℝ) (x y : V) :
    a • (x + y) = a • x + a • y := by
  Hint "Rewrite with `smul_add`, or close it directly with `exact smul_add a x y`."
  rw [smul_add]

NewTheorem smul_add

TheoremTab "LinearAlgebra"
