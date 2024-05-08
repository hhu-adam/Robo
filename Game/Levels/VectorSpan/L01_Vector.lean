import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- World "Matrix"
-- Level 1

-- Introduction

-- An $n$-dimensional vector is nothing but a function out of `Fin n`. For instance
-- a real-valued vector `x : Fin n → ℝ` assigns to each coordinate `i : Fin` a scalar
-- `x i : ℝ`. We can represent such a vector as `![x_1, ..., x_n]`.

-- Under the hood, `![a, b, c]` is syntax for `vecCons a (vecCons b (vecCons c vecEmpty))`.
-- where `Matrix.vecCons : α → (Fin n → α) → Fin (Nat.succ n) → α`

-- Since vectors are functions, we can define their addition and scalar multiplication pointwise.

#check Matrix.vecCons


open Real

example : ![(sqrt 3)/2, 1/2] + ![-(sqrt 3)/2, 1/2] = ![0, 1] := by
  --simp
  --ring
  funext i
  fin_cases i <;>
  simp <;>
  ring
