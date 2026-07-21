import Game.Metadata
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.PolynomialExp

World "Smooth"
Level 2

open Real Filter Topology Polynomial

Introduction "
The exponential function eventually outgrows every polynomial: for any
polynomial `p`, the quotient `p(x) / exp x` tends to `0` as `x → ∞`.
In Mathlib this is the theorem `Polynomial.tendsto_div_exp_atTop`.

As a warm-up, prove the special case where the polynomial is `X ^ 2`.
"

/---/
TheoremDoc Polynomial.tendsto_div_exp_atTop as "Polynomial.tendsto_div_exp_atTop"

/---/
TheoremDoc tendsto_sq_div_exp_atTop as "tendsto_sq_div_exp_atTop"

/- The square function divided by the exponential tends to `0` at infinity. -/
Statement tendsto_sq_div_exp_atTop :
    Tendsto (fun x : ℝ ↦ x ^ 2 / exp x) atTop (𝓝 0) := by
  Hint "[Hint qvxe] This is `Polynomial.tendsto_div_exp_atTop` applied to the
  polynomial `X ^ 2`. Start with `have h := (X ^ 2 : ℝ[X]).tendsto_div_exp_atTop`."
  have h := (X ^ 2 : ℝ[X]).tendsto_div_exp_atTop
  Hint "[Hint mzrp] Now `simp at h` evaluates the polynomial, turning `h` into
  exactly the goal."
  simp at h
  exact h

NewTheorem Polynomial.tendsto_div_exp_atTop
