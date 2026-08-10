import Game.Levels.Smooth.L05
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

World "Smooth"
Level 6

open Real

Introduction "Intro Smooth L06"

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
  Branch
    -- Hint (hidden := true) "[Hint pxe1b] Start with the polynomial: its derivative
    --   is `Polynomial.hasDerivAt`. Call it `hp`."
    have hp : HasDerivAt (fun x ↦ p.eval x) (p.derivative.eval x) x := by
      apply Polynomial.hasDerivAt
    Hint (strict := true) (hidden := true) "[Hint pxe2] Feed `{hp}` to `HasDerivAt.mul`; the leftover
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
        p.derivative.eval x * Real.exp (-x) + p.eval x * (Real.exp (-x) * -1) := by
      ring
    rw [hval]
    apply hmul
  Hint (hidden := true) "[Hint mbr1s6] First, establish a equality to transform the target
    derivative. Prove that `(p.derivative.eval x - p.eval x) * Real.exp (-x) =
      p.derivative.eval x * Real.exp (-x) + p.eval x * (Real.exp (-x) * -1)` by `have`. "
  have hval : (p.derivative.eval x - p.eval x) * Real.exp (-x) =
      p.derivative.eval x * Real.exp (-x) + p.eval x * (Real.exp (-x) * -1) := by
    ring
  Hint "[Hint rsmrhv] `rw` using `{hval}`."
  rw [hval]
  Hint "[Hint pxe3mb] Perfect! The product rule's derivative matches the current form."
  Hint (hidden := true) "[Hint pxe3mb2] Apply `HasDerivAt.mul`"
  apply HasDerivAt.mul
  · Hint (hidden := true) "[Hint sm6g1] Remember the theorem `Polynomial.hasDerivAt`."
    apply Polynomial.hasDerivAt p x
  · Hint (hidden := true) "[Hint sm6hen] You need to calculate the derivative of the form
    $e ^ (-x)$ now. Note that `HasDerivAt.exp`."
    apply HasDerivAt.exp
    Hint (hidden := true) "[Hint sm6hen2] Note that `hasDerivAt_neg`."
    apply hasDerivAt_neg


NewTheorem HasDerivAt.exp HasDerivAt.mul
