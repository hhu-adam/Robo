import Game.Levels.Smooth.L03
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.PolynomialExp

World "Smooth"
Level 4

open Real Filter Topology

Introduction "Intro Smooth L04:
The take-off function `f`
crushes any polynomial factor to `0` as `x → 0`, namely
`p.eval x⁻¹ * f x` tends to `0` as `x → 0` for any polynomial
`p`.
"

/-- -/
TheoremDoc tendsto_polynomial_inv_mul_zero as "tendsto_polynomial_inv_mul_zero" in "Function"

/-- -/
Statement tendsto_polynomial_inv_mul_zero (p : Polynomial ℝ) :
    Tendsto (fun x ↦ p.eval x⁻¹ * f x) (𝓝 0) (𝓝 0) := by
  Hint "[Hint tpimzsf] First, unfold the definition of `f` and simplify the expression using `simp`."
  simp [f]
  Hint "Note that for the case `x ≤ 0`, the function is constant."
  Hint (hidden := true) "Try "
  apply Tendsto.if tendsto_const_nhds
  simp
  have htop : Tendsto (fun (x : ℝ) ↦ x⁻¹) (𝓝[>] 0) atTop := by
    apply tendsto_inv_nhdsGT_zero
  have : Tendsto (fun x ↦ p.eval x⁻¹ / exp x⁻¹) (𝓝[>] 0) (𝓝 0) := by
    apply (Polynomial.tendsto_div_exp_atTop _).comp
    apply htop
  /-  -- mathlib proof
  refine this.congr' <| mem_of_superset self_mem_nhdsWithin fun x hx ↦ ?_
  simp [exp_neg, div_eq_mul_inv]
  -/
  apply Tendsto.congr' _ this
  filter_upwards
  simp [exp_neg, div_eq_mul_inv]

/---/
TheoremDoc Filter.Tendsto.if as "Filter.Tendsto.if" in "Function"

/---/
TheoremDoc Filter.Tendsto.congr' as "Filter.Tendsto.congr'"

/---/
TheoremDoc Real.exp_neg as "Real.exp_neg"

/---/
TheoremDoc tendsto_inv_nhdsGT_zero as "tendsto_inv_nhdsGT_zero" in "Function"

NewTheorem Filter.Tendsto.if tendsto_inv_nhdsGT_zero Filter.Tendsto.congr' Real.exp_neg div_eq_mul_inv
