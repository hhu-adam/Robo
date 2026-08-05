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
  Hint "[] Let `M` be an `R`-module, for each submodule `N`, and two elemenets `a`, `b` in `M`.
    In order to prove `a + b ∈ N`, it suffices to prove `a ∈ N` and `b ∈ N`."
  Hint (hidden := true) "[] Try to apply `add_mem`."
  apply add_mem
  · Hint (hidden := true) "[] Remember the `Submodule.mem_span_of_mem`. "
    apply Submodule.mem_span_of_mem
    assumption
  · Hint "[] Let `M` be a `R`-module and `N` be a submodule. Let `y` be an element in `N`, then
    for any element `r` in R, then `r • y` belongs to N."
    Hint (hidden := true) "[] This theorem is called `Submodule.smul_mem`. "
    apply Submodule.smul_mem
    Hint (hidden := true) "[] Remember `Submodule.mem_span_of_mem`."
    apply Submodule.mem_span_of_mem
    assumption

/---/
TheoremDoc AddMemClass.add_mem as "AddMemClass.add_mem" in "LinearAlgebra"

NewTheorem AddMemClass.add_mem
