import Game.Metadata

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

World "Span"
Level 7

Title "Span"

/- # Introduction

-/

open Real Function Set Finset BigOperators

example : Submodule ℝ (Fin 2 → ℝ) where
  carrier := {v : Fin 2 → ℝ | 3 * v 0 - v 1 = 0  }  -- { (![x, y] : Fin 2 → ℝ) | 3 * x - y = 0 } -- -- --
  add_mem' := by
    intro a b ha hb
    rw [mem_setOf] at *
    simp
    rw [mul_add]
    linear_combination ha + hb
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    dsimp at *
    rw [← sub_eq_zero.mp hx]
    linarith
