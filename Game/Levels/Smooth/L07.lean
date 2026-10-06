import Game.Levels.Smooth.L06

World "Smooth"
Level 7

open Real Polynomial

Introduction "Intro Smooth L07"

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
  Hint (strict := true) "[Hint pxe2] Now establish what the product rule, `HasDerivAt.mul`,
    gives you, using another `have`."
  have h := HasDerivAt.mul h_p h_expneg
  Hint (strict := true) "[Hint t99r1] Of course, you could also do this all in one step by chaining
    these rules together:
    ```
    have {h} := HasDerivAt.mul (p.hasDerivAt x) (HasDerivAt.comp x (hasDerivAt_exp (-x)) (hasDerivAt_neg x))
    ```
    Now remember `convert`.
    "
  Branch
    convert h
    Hint "[Hint 8riva] Better use `convert! {h} using 1`"
  convert! h using 1
  ring
  simp

/---/
TheoremDoc Polynomial.hasDerivAt as "hasDerivAt" in "R[X]"
/---/
TheoremDoc HasDerivAt.mul as "HasDerivAt.mul" in "HasDerivAt"
/---/
TheoremDoc Real.hasDerivAt_exp as "hasDerivAt_exp" in "Function"

NewTheorem Polynomial.hasDerivAt HasDerivAt.mul Real.hasDerivAt_exp
NewDefinition Polynomial.derivative

NewHiddenTactic «convert!»
