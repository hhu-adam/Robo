import Game.Metadata

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

World "Span"
Level 9

Title "Span"

/- # Introduction

The universal property of the submodule `Submodule.span K S`  spanned by a set
`S : Set M` is that `x ∈ Submodule.span K S` iff `x ∈ P` for any submodule `P`
containing `S`.

-/

open Real Function Set Finset BigOperators

Statement Submodule.subset_span {R : Type u_1} {M : Type u_4} [Semiring R]
    [AddCommMonoid M] [Module R M] {S : Set M} :
    S ⊆ ↑(Submodule.span R S) := by
  intro x hxS
  simp [Submodule.mem_span]
  intro P hP
  apply hP hxS
