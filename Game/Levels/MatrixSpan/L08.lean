import Game.Metadata




World "Span"
Level 8

Title "" -- "Span"

/- # Introduction

The universal property of the submodule `Submodule.span K S`  spanned by a set
`S : Set M` is that `x ∈ Submodule.span K S` iff `x ∈ P` for any submodule `P`
containing `S`.

-/

open Real Function Set Finset

/---/
TheoremDoc Submodule.mem_span_of_mem as "Submodule.mem_span_of_mem" in "LinearAlgebra"

Statement Submodule.mem_span_of_mem {V K : Type*} [Field K] [AddCommMonoid V]
    [Module K V] (M : Set V) {x : V} (h : x ∈ M) :
    x ∈ Submodule.span K M := by
  apply Submodule.subset_span
  assumption

TheoremTab "LinearAlgebra"
