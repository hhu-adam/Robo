import Game.Metadata

World "Span"
Level 4

Introduction "Intro Span L04"

/- # Introduction

The universal property of the submodule `Submodule.span K S`  spanned by a set
`S : Set M` is that `x ∈ Submodule.span K S` iff `x ∈ P` for any submodule `P`
containing `S`.

-/

open Real Function Set Finset

/--
Let `M` be an `R`-module, let `s` be set of M, let `x` be an element of s,
then x belongs to submodule spanned by s.
-/
TheoremDoc Submodule.mem_span_of_mem as "Submodule.mem_span_of_mem" in "LinearAlgebra"

Statement Submodule.mem_span_of_mem {V K : Type*} [Field K] [AddCommMonoid V]
    [Module K V] (M : Set V) {x : V} (h : x ∈ M) :
    x ∈ Submodule.span K M := by
  Hint "[Hint sp4subs] This is the previous level read pointwise: `Submodule.subset_span` says
    the whole set `M` sits inside its span."
  Hint (hidden := true) "[Hint sp4apsu] Apply `Submodule.subset_span`."
  apply Submodule.subset_span
  assumption

TheoremTab "LinearAlgebra"
