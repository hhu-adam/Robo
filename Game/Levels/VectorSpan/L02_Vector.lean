import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- World "Matrix"
-- Level 2

-- Introduction

-- Counter-intuitively, the empty vector is quite important in Lean since ultimately every
-- vector is built up from it.
-- `![a, b, c] = vecCons a (vecCons b (vecCons c vecEmpty))`



-- Vectors are functions and vector calculations are done componentwise.

open Real

#check Matrix.empty_eq
#check Matrix.zero_empty
theorem one_empty {α : Type*} [One α] : (1 : Fin 0 → ℝ) = ![] :=
  Matrix.empty_eq _


example {x₀ x₁ : ℝ} (h : ![x₀, x₁] = 0) : ![-x₀, -x₁] = 0 := by
  simp [Matrix.neg_cons]
  simp_all only [Matrix.cons_eq_zero_iff,
    Matrix.zero_empty,
    and_true,
    and_self]
