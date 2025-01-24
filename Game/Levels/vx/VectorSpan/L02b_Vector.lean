import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- World "Matrix"
-- Level 2

-- Introduction
-- A one dimensional vector is just a scalar.

open Real



#check smul_eq_mul
#check Matrix.zero_empty

example {x : ℝ} (h : ![x] = 0) : x = 0 := by
  simp at h


  -- -- simp_all only [Matrix.cons_eq_zero_iff,
  -- --   Matrix.zero_empty,
  -- --   and_true]
  -- apply Matrix.cons_eq_zero_iff.mp at h
  -- exact h.1
