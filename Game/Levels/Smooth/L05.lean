import Game.Levels.Smooth.L04
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Add

World "Smooth"
Level 5

open Polynomial

Introduction "Intro Smooth L05:
Time to differentiate. In the next few levels, you are going to use *product rule* and
*composition rule* to calculate some derivatives.

In this level you assemble those three bricks into the derivative of
$p(-x^{=1})$.
"

/---/
TheoremDoc Polynomial.hasDerivAt as "Polynomial.hasDerivAt"

/---/
TheoremDoc HasDerivAt.comp as "HasDerivAt.comp" in "Function"

/---/
TheoremDoc hasDerivAt_inv as "hasDerivAt_inv" in "Function"

/---/
TheoremDoc hasDerivAt_neg as "hasDerivAt_neg" in "Function"

/- The derivative of `x ↦ p(-x⁻¹)` at `x ≠ 0`, obtained from the chain rule. -/
Statement (p : ℝ[X]) (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun x ↦ p.eval (-x⁻¹))
      ((derivative p).eval (-x⁻¹) * (-1 * -(x ^ 2)⁻¹)) x := by
  Hint "[Hint dxq1] The goal is the triple composite `p ∘ neg ∘ inv`. Peel it
    apart one layer at a time with the chain rule `HasDerivAt.comp`."
  Branch
    -- Hint (hidden := true) "[Hint dxq1b] Start inside: the derivative of `x ↦ -x⁻¹`
    --   glues `hasDerivAt_neg` and `hasDerivAt_inv`. Build it as `hinner`."
    have hinner : HasDerivAt (fun x ↦ -x⁻¹) (-1 * -(x ^ 2)⁻¹) x := by
      apply (hasDerivAt_neg (x⁻¹)).comp x
      apply hasDerivAt_inv hx
    Hint (strict := true) (hidden := true) "[Hint dxq2] Now the polynomial `p` at the point `-x⁻¹` —
      that is `Polynomial.hasDerivAt`. Call it `hp`."
    have hp : HasDerivAt (fun x ↦ p.eval x) ((derivative p).eval (-x⁻¹)) (-x⁻¹) := by
      apply p.hasDerivAt
    Hint (hidden := true) "[Hint dxq3] A last `HasDerivAt.comp` joins the two:
      `apply hp.comp x hinner`."
    apply hp.comp x hinner
  Hint (hidden := true) "[Hint dxq1b] Start outside: the derivative of `{p}` is
    `derivative {p}`. Try to apply `HasDerivAt.comp x (Polynomial.hasDerivAt p _)`. "
  apply HasDerivAt.comp x (Polynomial.hasDerivAt p _)
  Hint "[Hint dxq2] Now the composition is `neg ∘ inv`. Note that we have theorem
    `hasDerivAt_neg`."
  Hint (hidden := true) "Try to apply `HasDerivAt.comp x (hasDerivAt_neg ({x}⁻¹))`. "
  apply HasDerivAt.comp x (hasDerivAt_neg (x⁻¹))
  Hint (hidden := true) "Note that the theorem `hasDerivAt_inv`."
  apply hasDerivAt_inv hx

NewTheorem Polynomial.hasDerivAt HasDerivAt.comp hasDerivAt_inv hasDerivAt_neg
NewDefinition Polynomial.derivative Polynomial.comp
