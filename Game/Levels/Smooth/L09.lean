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
  Hint "[Hint idp1] Induct on `n` with `induction n with`. The base case unfolds
    `P 0 = 1`; the successor step differentiates once and reuses the boss theorem
    `hasDerivAt_polynomial_eval_inv_mul`."
  induction n with
  | zero =>
    Hint (hidden := true) "[Hint idp2] `iteratedDeriv 0 f = f` and `P 0 = 1`, so
      after `funext x` finish with `rw [iteratedDeriv_zero, P, eval_one, one_mul]`."
    funext x
    rw [iteratedDeriv_zero, P, eval_one, one_mul]
  | succ n ih =>
    Hint (hidden := true) "[Hint idp3] Peel one derivative with `iteratedDeriv_succ`,
      rewrite by `ih` and unfold `P`, then the goal is exactly the `.deriv` of the
      boss theorem: `exact (hasDerivAt_polynomial_eval_inv_mul (P n) x).deriv`."
    funext x
    rw [iteratedDeriv_succ, ih, P]
    apply (hasDerivAt_polynomial_eval_inv_mul (P n) x).deriv

NewTheorem iteratedDeriv_zero iteratedDeriv_succ HasDerivAt.deriv
