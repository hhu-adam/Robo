import Game.Levels.Smooth.L08
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

World "Smooth"
Level 9

open Polynomial

noncomputable section

Introduction "
Differentiating `x ↦ p(x⁻¹) · f x` gives back a function of the *same shape*,
with a new polynomial — that was the boss level. Iterating, the `n`-th derivative
of `f` keeps this form, controlled by the polynomials

`P 0 = 1`,  `P (n+1) = X² · (P n - derivative (P n))`.

Prove `iteratedDeriv n f = fun x ↦ (P n)(x⁻¹) · f x` by induction on `n`, feeding
the boss theorem `hasDerivAt_polynomial_eval_inv_mul` into the successor step.
"

/-- The polynomials `P n` for which `iteratedDeriv n f = fun x ↦ (P n)(x⁻¹) · f x`. -/
def P : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => X ^ 2 * (P n - derivative (P n))

/-- The polynomials `P n` with `P 0 = 1` and `P (n+1) = X² · (P n - derivative (P n))`. -/
DefinitionDoc P as "P"

/---/
TheoremDoc iteratedDeriv_zero as "iteratedDeriv_zero"

/---/
TheoremDoc iteratedDeriv_succ as "iteratedDeriv_succ"

/---/
TheoremDoc HasDerivAt.deriv as "HasDerivAt.deriv"

/-- The `n`-th derivative of `f` is `(P n)(x⁻¹) · f x`. -/
TheoremDoc iteratedDeriv_eq_poly as "iteratedDeriv_eq_poly"

/- The `n`-th derivative of `f` is `(P n)(x⁻¹) · f x`. -/
Statement iteratedDeriv_eq_poly (n : ℕ) :
    iteratedDeriv n f = fun x ↦ (P n).eval x⁻¹ * f x := by
  Hint "[Hint idp1] Process by induction on `n`."
  induction n with n ih
  · Hint (hidden := true) "[Hint idp2] `0`-th derivative is the function itself."
    Branch
      funext x
      Hint "[sm9it] `rw` the goal with `iteratedDeriv_zero`."
      rw [iteratedDeriv_zero, P, eval_one, one_mul]
    simp_log [P]
  · Hint "[Hint idp3] Peel one derivative, then you can apply the induction hypothesis. "
    funext x
    Hint (hidden := true) "[sm9ritsc] `rw` the goal with `iteratedDeriv_succ`"
    rw [iteratedDeriv_succ, ih]
    Hint "[sm9ristp] Perfect! Now unfold the definition of `P` by `rw [P]`."
    rw [P]
    Hint (hidden := true) "Remember the theorems `HasDerivAt.deriv` and
      `hasDerivAt_polynomial_eval_inv_mul`."
    apply HasDerivAt.deriv
    apply hasDerivAt_polynomial_eval_inv_mul

/---/
TheoremDoc Polynomial.eval_one as "Polynomial.eval_one"

/---/
TheoremDoc one_mul as "one_mul"

NewTheorem iteratedDeriv_zero iteratedDeriv_succ HasDerivAt.deriv Polynomial.eval_one one_mul
NewDefinition P
