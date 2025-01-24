import Game.Metadata

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

import Game.Levels.MatrixSpan.L10

World "Span"
Level 11

Title "Span"

/- # Introduction

The universal property of the submodule `Submodule.span K S`  spanned by a set
`S : Set M` is that `x ∈ Submodule.span K S` iff `x ∈ P` for any submodule `P`
containing `S`.

-/

open Real Function Set Finset BigOperators

Statement {V K : Type _} [Field K] [AddCommMonoid V] [Module K V] (M : Set V) {x y : V}
    (h₁ : x ∈ M) (h₂ : y ∈ M) :
    x + (2 : K) • y ∈ Submodule.span K M := by
  apply add_mem
  apply Submodule.mem_span_of_mem
  assumption
  apply Submodule.smul_mem
  apply Submodule.mem_span_of_mem
  assumption
