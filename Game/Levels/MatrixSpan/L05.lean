import Game.Metadata
import Game.Levels.MatrixSpan.L04

World "Span"
Level 5

Introduction "Intro Span L05"

/- # Introduction

The universal property of the submodule `Submodule.span K S`  spanned by a set
`S : Set M` is that `x ∈ Submodule.span K S` iff `x ∈ P` for any submodule `P`
containing `S`.

-/

open Real Function Set Finset

Statement {V : Type*} [AddCommMonoid V] [Module ℝ V] (M : Set V) {x y : V}
    (h₁ : x ∈ M) (h₂ : y ∈ M) :
    x + (2 : ℝ) • y ∈ Submodule.span ℝ M := by
  Hint "[Hint sp5addm] A submodule is closed under addition, so it is enough to place the two
    summands in the span separately."
  Hint (hidden := true) "[Hint sp5aplm] Try to apply `add_mem`."
  apply add_mem
  · Hint (hidden := true) "[Hint sp5msom] `Submodule.mem_span_of_mem` moves membership in `M`
      into the span."
    apply Submodule.mem_span_of_mem
    assumption
  · Hint "[Hint sp5smul] A submodule is closed under scalar multiplication as well: if `y` lies
      in it, so does `r • y` for every scalar `r`."
    Hint (hidden := true) "[Hint sp5smmb] This theorem is called `Submodule.smul_mem`."
    apply Submodule.smul_mem
    Hint (hidden := true) "[Hint sp5msom] `Submodule.mem_span_of_mem` moves membership in `M`
      into the span."
    apply Submodule.mem_span_of_mem
    assumption

/--
Let `M` be an `R`-module, let `x y` be elements in `M`, then `x + y` is an element
in `M`.
-/
TheoremDoc AddMemClass.add_mem as "AddMemClass.add_mem" in "LinearAlgebra"

/- Comment: Should we keep the namespace `AddMemClass` in this theorem.-/
NewTheorem AddMemClass.add_mem
