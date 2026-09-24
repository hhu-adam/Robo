import Game.Levels.Smooth.L03

World "Smooth"
Level 4

open Real Filter Topology STakeOff Polynomial

Introduction "Intro Smooth L04"

/-- -/
TheoremDoc tendsto_polynomial_inv_mul_zero as "tendsto_polynomial_inv_mul_zero" in "Function"

/-- -/
Statement tendsto_polynomial_inv_mul_zero (p : Polynomial ℝ) :
    Tendsto (fun x ↦ p.eval x⁻¹ * f x) (𝓝 0) (𝓝 0) := by
  Hint "[Hint sm4bgf] The take-off function `f`
    crushes any polynomial factor to `0` as `x → 0`, namely
    `p.eval x⁻¹ * f x` tends to `0` as `x → 0` for any polynomial
    `p`.

    First, unfold the definition of f and simplify the expression using `simp`."
  simp [f]
  Hint "[Hint qq87t] Try `Tendsto.if`."
  apply Tendsto.if
  Hint "[Hint xcip8] Perfect.  Now you have cut the function in two halves, and have two goals.
    First, need to show that left half of function tends to `0` as `x → 0` “from the left”.
    If you like, you can make the goal more readable with:
    ```
    change Tendsto (fun (x : ℝ) ↦ 0) (𝓝[≤] 0) (𝓝 0)
    ```
    In any case, note that here the function is constant."
  change Tendsto (fun (x : ℝ) ↦ 0) (𝓝[≤] 0) (𝓝 0)
  Hint (hidden := true) "[Hint lpk2t] Remember `tendsto_const_nhds`."
  apply tendsto_const_nhds
  Hint "[Hint gh8td] Second, need to show that right half of function tends to `0` as `x → 0`
    “from the right”.
    But “from the right” is not written nicely.
    Change `¬ x ≤ 0` to `0 < x`, using `not_le` or just `simp`."
  simp
  Hint "[Hint 65tuz] Again, can make goal more readable with `change` – the complicated filter
    can be written as `𝓝[>] 0`.
    Also, pull the minus out of the `exp` using `simp_rw` and `exp_neg`."
  simp_rw [exp_neg]
  Hint (strict := true) "[Hint 4f4o8] This is `x ↦ p.eval x / exp x` composed with `x ↦ x⁻¹`).
     The theorem `Tendsto.comp` says how limits behave under composition.
     First establish how the two functions behave:
     ```
     Tendsto (fun (x : ℝ) ↦ eval x p / rexp x) atTop (𝓝 0)
     ```
     and
     ```
     Tendsto (fun (x : ℝ) ↦ x⁻¹) (𝓝[>] 0 ) atTop
     ```
     "
  have h1 : Tendsto (fun (x : ℝ) ↦ eval x p / rexp x) atTop (𝓝 0) := by
    Hint (hidden := true) "[Hint hi2ko] Remember `tendsto_div_exp_atTop`."
    apply tendsto_div_exp_atTop
  have h2 : Tendsto (fun (x : ℝ) ↦ x⁻¹) (𝓝[>] 0 ) atTop := by
    Hint "[Hint mbyuc] This is precisely `tendsto_inv_nhdsGT_zero`."
    apply tendsto_inv_nhdsGT_zero
  Hint (hidden := true) "[Hint 6bxi7] You're in good shap.  Now apply `Tendsto.comp`."
  apply Tendsto.comp h1 h2

  /-
  Hint "[Hint sm4cgr] If `f₁` is eventually equal to `f₂` along a filter `l₁`, then `f₁` tending to
    `l₂` along `l₁` implies `f₂` does too. This is `Tendsto.congr'` in Mathlib."
  Hint (hidden := true) "[Hint sm4apc] Apply `Tendsto.congr' _ {this}`."
  apply Tendsto.congr' _ this
  -/

/---/
TheoremDoc Filter.Tendsto.if as "Filter.Tendsto.if" in "Function"

--/---/
--TheoremDoc Filter.Tendsto.congr' as "Filter.Tendsto.congr'"

--/---/
--TheoremDoc Filter.Tendsto.congr as "Filter.Tendsto.congr"

/---/
TheoremDoc Real.exp_neg as "Real.exp_neg"

/---/
TheoremDoc tendsto_inv_nhdsGT_zero as "tendsto_inv_nhdsGT_zero" in "Function"

NewTheorem Filter.Tendsto.if tendsto_inv_nhdsGT_zero Real.exp_neg
--Filter.Tendsto.congr' Filter.Tendsto.congr

NewTactic change -- could be introduced earlier
