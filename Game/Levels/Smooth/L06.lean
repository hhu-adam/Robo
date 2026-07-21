import Game.Levels.Smooth.L05
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

World "Smooth"
Level 6

open Real

Introduction "
Products are handled by the *product rule* `HasDerivAt.mul`, and the exponential
by the chain-rule shortcut `HasDerivAt.exp`. Together they cover any mix of
polynomials and exponentials.

In this level you differentiate `x ↦ p(x) · exp (-x)` — the exact building block
that the final level will need.
"

/---/
TheoremDoc HasDerivAt.exp as "HasDerivAt.exp"

/---/
TheoremDoc HasDerivAt.mul as "HasDerivAt.mul"

/- The derivative of `x ↦ p(x) · exp (-x)`, from the product rule. -/
Statement (x : ℝ) {p : Polynomial ℝ} :
    HasDerivAt (fun x ↦ p.eval x * Real.exp (-x))
      ((p.derivative.eval x - p.eval x) * Real.exp (-x)) x := by
  Hint "[Hint pxe1] Differentiate the two factors, then join them with the
    product rule `HasDerivAt.mul`."
  Hint (hidden := true) "[Hint pxe1b] Start with the polynomial: its derivative
    is `Polynomial.hasDerivAt`. Call it `hp`."
  have hp : HasDerivAt (fun x ↦ p.eval x) (p.derivative.eval x) x := by
    apply p.hasDerivAt
  Hint (hidden := true) "[Hint pxe2] Feed `hp` to `HasDerivAt.mul`; the leftover
    `exp (-x)` factor is `HasDerivAt.exp` applied to `hasDerivAt_neg`."
  have hmul : HasDerivAt (fun x ↦ p.eval x * Real.exp (-x))
      (p.derivative.eval x * Real.exp (-x) +
        p.eval x * (Real.exp (-x) * -1)) x := by
    apply HasDerivAt.mul hp
    · apply HasDerivAt.exp
      apply hasDerivAt_neg
  Hint (hidden := true) "[Hint pxe3] The product rule's derivative matches the
    goal up to algebra — bridge them with an equality closed by `ring`, then
    `rw` and finish."
  have hval : (p.derivative.eval x - p.eval x) * Real.exp (-x) =
      p.derivative.eval x * Real.exp (-x) +
        p.eval x * (Real.exp (-x) * -1) := by
    ring
  rw [hval]
  apply hmul

NewTheorem HasDerivAt.exp HasDerivAt.mul
