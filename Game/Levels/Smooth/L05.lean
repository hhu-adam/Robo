import Game.Levels.Smooth.L04
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Add

World "Smooth"
Level 5

open Polynomial

Introduction "
Time to differentiate. Recall that `HasDerivAt g g' a` records that `g` has
derivative `g'` at the point `a`.

The strength of this predicate is that derivatives *compose*: the chain rule
`HasDerivAt.comp` builds the derivative of a composite from the derivatives of
its pieces. So a formula like `x ↦ p(-x⁻¹)` is no harder than the bricks it is
made of — the inverse, the negation, and the polynomial `p`.

In this level you assemble those three bricks into the derivative of
`x ↦ p(-x⁻¹)`.
"

/---/
TheoremDoc Polynomial.hasDerivAt as "Polynomial.hasDerivAt"

/---/
TheoremDoc HasDerivAt.comp as "HasDerivAt.comp"

/---/
TheoremDoc hasDerivAt_inv as "hasDerivAt_inv"

/---/
TheoremDoc hasDerivAt_neg as "hasDerivAt_neg"

/- The derivative of `x ↦ p(-x⁻¹)` at `x ≠ 0`, obtained from the chain rule. -/
Statement (p : ℝ[X]) (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun x ↦ p.eval (-x⁻¹))
      ((derivative p).eval (-x⁻¹) * (-1 * -(x ^ 2)⁻¹)) x := by
  Hint "[Hint dxq1] The goal is the triple composite `p ∘ neg ∘ inv`. Peel it
    apart one layer at a time with the chain rule `HasDerivAt.comp`."
  Hint (hidden := true) "[Hint dxq1b] Start inside: the derivative of `x ↦ -x⁻¹`
    glues `hasDerivAt_neg` and `hasDerivAt_inv`. Build it as `hinner`."
  have hinner : HasDerivAt (fun x ↦ -x⁻¹) (-1 * -(x ^ 2)⁻¹) x := by
    apply (hasDerivAt_neg (x⁻¹)).comp x
    apply hasDerivAt_inv hx
  Hint (hidden := true) "[Hint dxq2] Now the polynomial `p` at the point `-x⁻¹` —
    that is `Polynomial.hasDerivAt`. Call it `hp`."
  have hp : HasDerivAt (fun x ↦ p.eval x) ((derivative p).eval (-x⁻¹)) (-x⁻¹) := by
    apply p.hasDerivAt
  Hint (hidden := true) "[Hint dxq3] A last `HasDerivAt.comp` joins the two:
    `apply hp.comp x hinner`."
  apply hp.comp x hinner


NewTheorem Polynomial.hasDerivAt HasDerivAt.comp hasDerivAt_inv hasDerivAt_neg
