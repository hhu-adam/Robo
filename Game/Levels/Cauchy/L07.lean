import Game.Levels.Cauchy.L06

World "Cauchy"
Level 7

namespace Real
open Polynomial

Introduction "Intro Cauchy L07"

/- The derivative of `x ↦ p(x) · exp (-x)`, from the product rule. -/
Statement (x : ℝ) {p : Polynomial ℝ} :
    HasDerivAt (fun x ↦ p.eval x * exp (-x))
      ((p.derivative.eval x - p.eval x) * exp (-x)) x := by
  Hint (strict := true) "[Hint pxe1] Differentiate the two factors, then join them with the
    product rule `HasDerivAt.mul`.  You already know how to differentiate the polynomial.
    For the other factor, use `hasDerivAt_neg`, `hasDerivAt_exp` at `HasDerivAt.comp`.
    "
  have h_p := p.hasDerivAt x
  have h_neg := hasDerivAt_neg x
  have h_exp := hasDerivAt_exp (-x) --h_neg
  have h_expneg := HasDerivAt.comp x h_exp h_neg
  clear h_neg h_exp
  Hint (strict := true) "[Hint pxe2] Now establish what the product rule, encoded by the
    new theorem `HasDerivAt.mul`."
  have h := HasDerivAt.mul h_p h_expneg
  --have {h} := HasDerivAt.mul (p.hasDerivAt x) (HasDerivAt.comp x (hasDerivAt_exp (-x)) (hasDerivAt_neg x))
  Hint (strict := true) "[Hint t99r1] Remember `convert`."
  Branch
    convert h
    Hint "[Hint 8riva] Better use `convert! {h} using 1`"
  convert! h using 1
  ring
  simp

/---/
TheoremDoc HasDerivAt.mul as "HasDerivAt.mul" in "HasDerivAt"
/---/
TheoremDoc Real.hasDerivAt_exp as "hasDerivAt_exp" in "Function"
/--
This root level version of `hasDerivAt_exp` should not be used in the game.
It is present here only so that ambiguous invocations of `Real.hasDerivAt_exp` pass the game engine's
inventory checks. Lean can often figure out the disambiguity between the root version and the Real
version of this theorem from the types passed to theorem, but the game engine currently cannot.
-/
TheoremDoc hasDerivAt_exp as "(hasDerivAt_exp)"

NewTheorem HasDerivAt.mul Real.hasDerivAt_exp hasDerivAt_exp

NewHiddenTactic «convert!»
