import Game.Metadata

World "Smooth"
Level 2

open Real Filter Topology Polynomial

Introduction "Intro Smooth L02
"

/---/
TheoremDoc Polynomial.tendsto_div_exp_atTop as "Polynomial.tendsto_div_exp_atTop"

/---/
TheoremDoc tendsto_sq_div_exp_atTop as "tendsto_sq_div_exp_atTop"

/- The square function divided by the exponential tends to `0` at infinity. -/
Statement tendsto_sq_div_exp_atTop :
    Tendsto (fun x : ℝ ↦ x ^ 2 / exp x) atTop (𝓝 0) := by
  Hint (strict := true) "[] For any
  polynomial `p`, the quotient `p(x) / exp x` tends to `0` as `x → ∞`.
  As a warm-up, prove the special case where the polynomial is `X ^ 2`."
  Hint (strict := true) "[] First, establish `Tendsto (fun (x : ℝ) ↦ (X ^ 2).eval x / exp x) atTop (𝓝 0)` by `have`."
  have h : Tendsto (fun (x : ℝ) ↦ (X ^ 2).eval x / exp x) atTop (𝓝 0) := by
    Hint (hidden := true) "[Hint ptdeat] Try `Polynomial.tendsto_div_exp_atTop`."
    apply Polynomial.tendsto_div_exp_atTop
  Hint "[Hint mzrp] Perfect, you're on track. Now try to simplify `{h}` by evaluating the polynomial."
  simp at h
  apply h

NewTheorem Polynomial.tendsto_div_exp_atTop
NewDefinition Real.exp
