import Game.Metadata
import Game.Levels.MatrixSpan.L04

World "Span"
Level 6

Introduction "Intro Span L06"

/- # Introduction

The universal property of the submodule `Submodule.span K S`  spanned by a set
`S : Set M` is that `x ∈ Submodule.span K S` iff `x ∈ P` for any submodule `P`
containing `S`.

-/

open Real Function Set Finset

Statement {n : ℕ} (A : Mat[n,n][ℝ]) : A * A ∈ Submonoid.powers A := by
  Hint "[Hint sp6powr] Lying in `Submonoid.powers {A}` means being *some* power of {A},
    so you have to exhibit an exponent `k` with `{A} ^ k` equal to the matrix in question."
  Hint (hidden := true) "[Hint sp6use2] Here that exponent is `2`, so `use 2`."
  use 2
  Branch
    simp [pow_two]
  simp
  rw [pow_two]


/---/
TheoremDoc pow_two as "pow_two" in "+ *"

NewTheorem pow_two
NewDefinition Submonoid.powers
TheoremTab "LinearAlgebra"
