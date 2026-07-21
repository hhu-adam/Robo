import Game.Levels.Smooth.L09
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

World "Smooth"
Level 10

open Polynomial

Introduction "
The pay-off. Since the `n`-th derivative of `f` is `(P n)(x⁻¹) · f x` and
`f 0 = 0`, plugging in `x = 0` annihilates every derivative: `f` is *infinitely
flat* at `0`. This is what makes the take-off function smooth across the seam.
"

/- Every iterated derivative of `f` vanishes at `0`. -/
Statement iteratedDeriv_f_zero (n : ℕ) : iteratedDeriv n f 0 = 0 := by
  Hint "[Hint idz1] Rewrite with the formula from the previous level, then the
    factor `f 0` is `0` by `zero_of_nonpos`."
  Hint (hidden := true) "[Hint idz2] `rw [iteratedDeriv_eq_poly]`, then close with
    `zero_of_nonpos (le_refl 0)` and `mul_zero`."
  rw [iteratedDeriv_eq_poly]
  simp [zero_of_nonpos]
