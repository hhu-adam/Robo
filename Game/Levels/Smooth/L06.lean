import Game.Levels.Smooth.L05

World "Smooth"
Level 6

open Real Polynomial

Introduction "Intro Smooth L06"

/---/
TheoremDoc HasDerivAt.exp as "HasDerivAt.exp"

/---/
TheoremDoc HasDerivAt.mul as "HasDerivAt.mul"

/- The derivative of `x ↦ p(x) · exp (-x)`, from the product rule. -/
Statement (x : ℝ) {p : Polynomial ℝ} :
    HasDerivAt (fun x ↦ p.eval x * exp (-x))
      ((p.derivative.eval x - p.eval x) * exp (-x)) x := by
  Hint (strict := true) "[Hint pxe1] Differentiate the two factors, then join them with the
    product rule `HasDerivAt.mul`.  You already know how to differentiate the polynomial.
    For the other factor, use `hasDerivAt_neg` and `HasDerivAt.exp`.
    "
  Hint (strict := true) (hidden := true) "[Hint hiovs] `HasDerivAt.exp` computes the derivate
    of `exp f` at `x`, given the derivative of `f`.
    So it takes a proof `h_f : HasDerivAt f f' x` as argument."
  have h_p := p.hasDerivAt x
  have h_neg := hasDerivAt_neg x
  have h_exp := HasDerivAt.exp h_neg
  clear h_neg
  Hint (strict := true) "[Hint pxe2] Now establish what the product rule, `HasDerivAt.mul`,
    gives you, using another `have`."
  have h := HasDerivAt.mul h_p h_exp
  Hint (strict := true) "[Hint t99r1] Almost there.  If you compare `{h}` to your goal,
    you'll find that the essential difference can be bridged by the following equality:
    ```
    (p.derivative.eval x - p.eval x) * exp (-x) = p.derivative.eval x * exp (-x) + p.eval x * (exp (-x) * -1)
    ```
    Establish it and use it.
    "
  have hf' : (p.derivative.eval x - p.eval x) * exp (-x) =
      p.derivative.eval x * exp (-x) + p.eval x * (exp (-x) * -1) := by
    ring
  rw [hf']
  apply h


NewTheorem HasDerivAt.exp HasDerivAt.mul
