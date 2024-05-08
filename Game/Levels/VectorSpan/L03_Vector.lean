import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- World "Matrix"
-- Level 2

-- Introduction
--

open Real

example : sqrt 2 • ![(sqrt 2)/2, 0] + sqrt 2 • ![0, (sqrt 2)/2] = ![1, 1] := by
  simp only [Matrix.smul_cons]
  simp only [smul_eq_mul]
  simp only [mul_zero]
  simp only [Matrix.smul_empty]

  simp only [Matrix.zero_empty]

  smul_eq_mul, mul_zero, Matrix.smul_empty, Matrix.add_cons,
    Matrix.head_cons, add_zero, Matrix.tail_cons, zero_add, Matrix.empty_add_empty]
  ring
  norm_num

#check Matrix.smul_cons
