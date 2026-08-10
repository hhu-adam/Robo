import Game.Levels.Smooth.L09
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

World "Smooth"
Level 10

open Polynomial STakeOff

Introduction "Intro Smooth L10"

/-- Every iterated derivative of `f` vanishes at `0`, so `f` is infinitely flat there. -/
TheoremDoc iteratedDeriv_f_zero as "iteratedDeriv_f_zero" in "Function"

/- Every iterated derivative of `f` vanishes at `0`. -/
Statement iteratedDeriv_f_zero (n : ℕ) : iteratedDeriv n f 0 = 0 := by
  Hint "[Hint sm10bgf] By the previous level every derivative of `f` still carries the factor
    `f x`, and `f` vanishes on the whole left half-line. So at `x = 0` all of them are `0`:
    `f` is *infinitely flat* there — smooth, yet nowhere near its Taylor series at `0`."
  Hint "[Hint idz1] Rewrite with the formula from the previous level, and note that `f 0 = 0`."
  Hint (hidden := true) "[Hint idz2] `rw [iteratedDeriv_eq_poly]`."
  rw [iteratedDeriv_eq_poly]
  simp [zero_of_nonpos]
