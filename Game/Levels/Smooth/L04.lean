import Game.Levels.Smooth.L03

World "Smooth"
Level 4

open Real Filter Topology STakeOff

Introduction "Intro Smooth L04"

/-- -/
TheoremDoc tendsto_polynomial_inv_mul_zero as "tendsto_polynomial_inv_mul_zero" in "Function"

/-- -/
Statement tendsto_polynomial_inv_mul_zero (p : Polynomial ℝ) :
    Tendsto (fun x ↦ p.eval x⁻¹ * f x) (𝓝 0) (𝓝 0) := by
  Hint "[Hint sm4bgf] The take-off function `f`
  crushes any polynomial factor to `0` as `x → 0`, namely
  `p.eval x⁻¹ * f x` tends to `0` as `x → 0` for any polynomial
  `p`."
  Hint "[Hint tpimzsf] First, unfold the definition of `f` and simplify the expression using `simp`."
  simp [f]
  Hint "[Hint sm4tcnst] Note that for the case `x ≤ 0`, the function is constant."
  Hint (hidden := true) "Try to combine `Tendsto.if` and `tendsto_const_nhds`."
  apply Tendsto.if tendsto_const_nhds
  Hint "[Hint sm4nle] The goal now contains a `¬ x ≤ 0`. Rewrite it with `not_le`, or just `simp`."
  simp
  Hint "[Hint sm4hdve] Establish `Tendsto (fun x ↦ p.eval x⁻¹ / exp x⁻¹) (𝓝[>] 0) (𝓝 0)` by `have`.
    Remember the theorem `Polynomial.tendsto_div_exp_atTop` in Level 2. "
  have : Tendsto (fun x ↦ p.eval x⁻¹ / exp x⁻¹) (𝓝[>] 0) (𝓝 0) := by
    Hint (hidden := true) "[Hint sm4tcpt] This is `p.eval x / exp x` compose with
      inverse function. Now apply `Tendsto.comp (Polynomial.tendsto_div_exp_atTop _)`"
    apply Tendsto.comp (Polynomial.tendsto_div_exp_atTop _)
    Hint (hidden := true) "[Hint sm4iiz] Note that `tendsto_inv_nhdsGT_zero`."
    apply tendsto_inv_nhdsGT_zero
  /-  -- mathlib proof
  refine this.congr' <| mem_of_superset self_mem_nhdsWithin fun x hx ↦ ?_
  simp [exp_neg, div_eq_mul_inv]
  -/
  Hint "[Hint sm4cgr] If `f₁` is eventually equal to `f₂` along a filter `l₁`, then `f₁` tending to
    `l₂` along `l₁` implies `f₂` does too. This is `Tendsto.congr'` in Mathlib."
  Hint (hidden := true) "[Hint sm4apc] Apply `Tendsto.congr' _ {this}`."
  apply Tendsto.congr' _ this
  Hint (hidden := true) "[Hint sm4fup] Remember `filter_upwards`!"
  filter_upwards
  Hint (hidden := true) "[Hint sm4eng] Try to simplify with theorem `exp_neg` and then `grind`."
  simp [exp_neg]
  grind

/---/
TheoremDoc Filter.Tendsto.if as "Filter.Tendsto.if" in "Function"

/---/
TheoremDoc Filter.Tendsto.congr' as "Filter.Tendsto.congr'"

/---/
TheoremDoc Filter.Tendsto.congr as "Filter.Tendsto.congr"

/---/
TheoremDoc Real.exp_neg as "Real.exp_neg"

/---/
TheoremDoc tendsto_inv_nhdsGT_zero as "tendsto_inv_nhdsGT_zero" in "Function"

NewTheorem Filter.Tendsto.if tendsto_inv_nhdsGT_zero Filter.Tendsto.congr'
  Filter.Tendsto.congr Real.exp_neg
