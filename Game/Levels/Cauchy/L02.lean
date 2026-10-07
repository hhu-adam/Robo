import Game.Levels.Cauchy.L01

World "Cauchy"
Level 2

open Real Filter Topology Polynomial

Introduction "Intro Cauchy L02"

/---/
TheoremDoc tendsto_sq_div_exp_atTop as "tendsto_sq_div_exp_atTop"

/- The square function divided by the exponential tends to `0` at infinity. -/
Statement tendsto_sq_div_exp_atTop :
    Tendsto (fun x : ℝ ↦ x ^ 2 / exp x) atTop (𝓝 0) := by
  Hint (strict := true) "[Hint 2vkf4]
    `exp` is the exponential function.

    For any polynomial `p`, the quotient `p(x) / exp x`
    tends to `0` as `x → ∞`.  This is known as `tendsto_div_exp_atTop`.

    First, establish `x^2 = (X^2).eval x`.
    "
  Hint (strict := true) (hidden := true) "[Hint u6qjy] Start with `have`."
  have h (x : ℝ): x^2 = (X^2).eval x := by
    Hint (hidden := true) "[Hint z5r1d] This is just `simp`."
    simp
  Hint "[Hint r8yz8] Now you want to use `{h}` to rewrite the goal.
    But `rw` does not work well under quantifiers.
    New tactic `simp_rw` works better."
  simp_rw [h]
  Hint (hidden := true) "[Hint ewvsj] Exactly new theorem: `tendsto_div_exp_atTop`."
  apply tendsto_div_exp_atTop

/---/
TheoremDoc Polynomial.tendsto_div_exp_atTop as "Polynomial.tendsto_div_exp_atTop"

NewTheorem Polynomial.tendsto_div_exp_atTop
NewDefinition Real.exp
NewTactic simp_rw
