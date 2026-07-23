import Game.Metadata




World "Span"
Level 4

Title "" -- "Span"

/- # Introduction

The universal property of the submodule `Submodule.span K S`  spanned by a set
`S : Set M` is that `x ∈ Submodule.span K S` iff `x ∈ P` for any submodule `P`
containing `S`.

-/

open Real Function Set Finset

/---/
TheoremDoc Submodule.subset_span as "Submodule.subset_span" in "LinearAlgebra"

Statement Submodule.subset_span {R : Type} {M : Type} [Semiring R]
    [AddCommMonoid M] [Module R M] {S : Set M} :
    S ⊆ ↑(Submodule.span R S) := by
  intro x hxS
  simp [Submodule.mem_span]
  intro P hP
  apply hP hxS

/---/
TheoremDoc Submodule.mem_span as "Submodule.mem_span" in "LinearAlgebra"

/-- `Submodule.span R S` is the smallest submodule containing the set `S`. -/
DefinitionDoc Submodule.span as "Submodule.span" in "LinearAlgebra"

NewTheorem Submodule.mem_span
NewDefinition Submodule.span
TheoremTab "LinearAlgebra"
