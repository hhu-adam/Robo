import Game.Metadata

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

import Game.Levels.MatrixSpan.L10

World "Span"
Level 12

Title "Span"

/- # Introduction

The universal property of the submodule `Submodule.span K S`  spanned by a set
`S : Set M` is that `x ∈ Submodule.span K S` iff `x ∈ P` for any submodule `P`
containing `S`.

-/

open Real Function Set Finset BigOperators

Statement {n : ℕ} (A : Mat[n,n][ℝ]) : A * A ∈ Submonoid.powers A := by
  apply MulMemClass.mul_mem -- what is this?
  iterate simp [Submonoid.mem_powers]
