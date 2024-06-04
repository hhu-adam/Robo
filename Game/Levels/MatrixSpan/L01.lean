import Game.Metadata

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

World "Span"
Level 1

Title "Span"

/- # Introduction

An `n`-dimensional vector is nothing but a function out of `Fin n`. For instance
a real-valued vector `x : Fin n → ℝ` assigns to each coordinate `i : Fin` a scalar
`x i : ℝ`.
We represent such a vector as `![x_1, ..., x_n]`.

Under the hood, `![a, b, c]` is syntax for `vecCons a (vecCons b (vecCons c vecEmpty))`.
where `Matrix.vecCons : α → (Fin n → α) → Fin (Nat.succ n) → α`

Counter-intuitively, the empty vector is quite important in Lean since ultimately every
vector is built up from it.

-/

open Real Function Set Finset BigOperators

Statement (a b c : ℝ) : ![a,b,c] 0 + ![a,b,c] 1 = a + b := by
  rfl
