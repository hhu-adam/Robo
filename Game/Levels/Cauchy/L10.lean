import Game.Levels.Cauchy.L09

World "Cauchy"
Level 10

open Polynomial Cauchy

noncomputable section

Introduction "Intro Cauchy L10"

/-- The polynomials `P n` for which `iteratedDeriv n f = fun x ↦ (P n)(x⁻¹) · f x`. -/
def Cauchy.P : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => X ^ 2 * (P n - derivative (P n))

/-- The polynomials `P n` with `P 0 = 1` and `P (n+1) = X² · (P n - derivative (P n))`. -/
DefinitionDoc P as "P"

/-- The `n`-th derivative of `f` is `(P n)(x⁻¹) · f x`. -/
TheoremDoc iteratedDeriv_eq_poly as "iteratedDeriv_eq_poly"

/- The `n`-th derivative of `f` is `(P n)(x⁻¹) · f x`. -/
Statement iteratedDeriv_eq_poly (n : ℕ) :
    iteratedDeriv n f = fun x ↦ (P n).eval x⁻¹ * f x := by
  #check P
  Hint "[Hint sm9bgf]
    For `f` as before, we now compute `iteratedDeriv n f`, the $n$-th derivative of f.

    The previous level showed that differentiating `x ↦ p(x⁻¹) · f x` gives
    back a function of the *same shape*, with `p` replaced by `X² · (p - derivative p)`.

    We can therefore express the derivatives in ferms of following, recursively defined
    family of polynomials `P : ℕ → ℝ[X]`:
    $$
    \\begin\{aligned}
     P(0)   &:= 1 \\\\ %(new line)
     P(n+1) &:= X^2 · (P (n) - \\mathrm\{derivate}(P(n)) )
    \\end\{aligned}
    $$
    "
  Hint (hidden := true) "[Hint idp1] Proceed by induction on `n`, obviously."
  induction n with n ih
  · Hint (hidden := true) "[Hint idp2] `0`-th derivative is the function itself – that's `simp`le."
    simp [P]
  · Hint "[Hint idp3] Peel one derivative, then you can apply the induction hypothesis.
    You will need `iteratedDeriv_succ`."
    Hint (hidden := true) "[Hint sm9ritsc] Start with `funext`"
    Branch
      rw [iteratedDeriv_succ]
      rw [ih]
    funext x
    rw [iteratedDeriv_succ, ih]
    Hint "[Hint sm9ristp] Perfect! Now unfold the definition of `P` with `rw [P]`."
    rw [P]
    Hint (hidden := true) "[Hint sm9hdap] Remember the theorems `HasDerivAt.deriv` and
      `hasDerivAt_polynomial_eval_inv_mul`."
    apply HasDerivAt.deriv
    apply hasDerivAt_polynomial_eval_inv_mul

/---/
TheoremDoc Polynomial.eval_one as "Polynomial.eval_one"
/---/
TheoremDoc iteratedDeriv_succ as "iteratedDeriv_succ"
/---/
TheoremDoc HasDerivAt.deriv as "HasDerivAt.deriv"


NewTheorem iteratedDeriv_succ HasDerivAt.deriv Polynomial.eval_one
NewDefinition P
