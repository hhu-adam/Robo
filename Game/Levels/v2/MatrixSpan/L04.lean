import Game.Metadata

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

World "Span"
Level 4

Title "Span"

/- # Introduction


-/

open Real Function Set Finset BigOperators

Statement {a b : ℝ} (h : 2 • ![a, -b] + - ![a + b, a - b] = ![0, 0]) :
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
