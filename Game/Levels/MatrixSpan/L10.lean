import Game.Metadata




import Game.Levels.MatrixSpan.L08

World "Span"
Level 10

Title "" -- "Span"

/- # Introduction

The universal property of the submodule `Submodule.span K S`  spanned by a set
`S : Set M` is that `x ∈ Submodule.span K S` iff `x ∈ P` for any submodule `P`
containing `S`.

-/

open Real Function Set Finset

Statement {n : ℕ} (A : Mat[n,n][ℝ]) : A * A ∈ Submonoid.powers A := by
  apply MulMemClass.mul_mem -- what is this?
  · simp [Submonoid.mem_powers]
  · simp [Submonoid.mem_powers]

/---/
TheoremDoc MulMemClass.mul_mem as "MulMemClass.mul_mem" in "LinearAlgebra"

/---/
TheoremDoc Submonoid.mem_powers as "Submonoid.mem_powers" in "LinearAlgebra"

NewTheorem MulMemClass.mul_mem Submonoid.mem_powers
