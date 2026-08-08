import Game.Metadata

World "Span"
Level 3

Introduction "Intro Span L03"

/- # Introduction

The universal property of the submodule `Submodule.span K S`  spanned by a set
`S : Set M` is that `x ∈ Submodule.span K S` iff `x ∈ P` for any submodule `P`
containing `S`.

-/

open Real Function Set Finset

/---/
TheoremDoc Submodule.subset_span as "Submodule.subset_span" in "LinearAlgebra"

Statement Submodule.subset_span {R : Type} {M : Type} [CommRing R]
    [AddCommMonoid M] [Module R M] {S : Set M} :
    S ⊆ ↑(Submodule.span R S) := by
  Hint "[Hint sp3smst] The span of `S` is the smallest submodule containing `S`, so every
    element of `S` already lies in it. Start from an arbitrary element of `S`."
  Hint (hidden := true) "[Hint sp3intx] Try `intro x hxS`."
  intro x hxS
  Hint "[Hint sp3msun] `Submodule.mem_span` is the universal property: `x` lies in the span of
    `S` exactly when it lies in every submodule containing S."
  simp [Submodule.mem_span]
  Hint (hidden := true) "[Hint sp3appp] Take such a submodule and feed it `{hxS}`."
  intro P hP
  apply hP hxS

/---/
TheoremDoc Submodule.mem_span as "Submodule.mem_span" in "LinearAlgebra"

NewTheorem Submodule.mem_span
NewDefinition Submodule.span
TheoremTab "LinearAlgebra"
