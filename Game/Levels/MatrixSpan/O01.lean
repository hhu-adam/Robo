import Game.Metadata




World "Span"
Level 1

Title "" -- "Span"

/- # Introduction

-/

open Real Function Set Finset

example : Submodule ℝ (Fin 2 → ℝ) where
  carrier := {v : Fin 2 → ℝ | 3 * v 0 - v 1 = 0}  -- { (![x, y] : Fin 2 → ℝ) | 3 * x - y = 0 } -- -- --
  add_mem' := by
    intro a b ha hb
    rw [mem_setOf] at *
    simp
    grind
  zero_mem' := by
    simp
  smul_mem' := by
    intro c x hx
    simp at hx ⊢
    grind
