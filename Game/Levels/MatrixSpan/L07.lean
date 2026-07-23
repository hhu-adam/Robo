import Game.Metadata




import Game.Levels.MatrixSpan.L05

World "Span"
Level 7

Title "" -- "Span"

/- # Introduction

The universal property of the submodule `Submodule.span K S`  spanned by a set
`S : Set M` is that `x ∈ Submodule.span K S` iff `x ∈ P` for any submodule `P`
containing `S`.

-/

open Real Function Set Finset

Statement {n : ℕ} (A : Mat[n,n][ℝ]) : A * A ∈ Submonoid.powers A := by
  use 2
  simp
  rw [pow_two]


/---/
TheoremDoc pow_two as "pow_two" in "+ *"

/-- `Submonoid.powers A` is the submonoid of all powers `A ^ n` of `A`. -/
DefinitionDoc Submonoid.powers as "Submonoid.powers" in "LinearAlgebra"

NewTheorem pow_two
NewDefinition Submonoid.powers
TheoremTab "LinearAlgebra"
