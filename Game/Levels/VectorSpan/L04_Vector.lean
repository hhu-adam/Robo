import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- World "Matrix"
-- Level 2

-- Introduction
-- Since vectors are functions we can

open Real


example {a : ℝ} (h : a + a = 0) : a = 0 := by
  simp_all only [add_self_eq_zero]

#check List.ofFn


example {a b : ℝ} (h : 2 • ![a, -b] + - ![a + b, a - b] = ![0, 0]) :
    a = 0 ∧ b = 0 := by
  simp at h
  conv at h =>
    lhs
    ring
  --constructor
  -- ...
  apply congr_fun at h
  have h₁ : a - b = 0 := h 0
  have h₂ : -a - b = 0 := h 1
  rw [eq_of_sub_eq_zero h₁] at *
  have : - b = 0 := by
    apply add_self_eq_zero.mp at h₂
    exact h₂
  simp only [and_self]
  apply neg_eq_zero.mp this




  --have : b = 0 := by simp [neg_add, eq_of_neg_eq_zero h₂, ]
  -- fin_cases
