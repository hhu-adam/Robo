import Game.Levels.Cauchy.L04

World "Cauchy"
Level 5

open Real Filter Topology Cauchy Polynomial

Introduction "Intro Cauchy L05"

/-- -/
TheoremDoc tendsto_polynomial_inv_mul_zero as "tendsto_polynomial_inv_mul_zero" in "Function"

Statement tendsto_polynomial_inv_mul_zero (p : Polynomial ℝ) :
    Tendsto (fun x ↦ p.eval x⁻¹ * f x) (𝓝 0) (𝓝 0) := by
  Hint "[Hint sm4bgf] It is actually true that the take-off function `f`
    crushes any polynomial factor to `0` as `x → 0`, i.e. that
    `p.eval x⁻¹ * f x` tends to `0` as `x → 0` for any polynomial
    `p`.

    First, unfold the definition of f and simplify the expression using `simp`."
  simp [f]
  Hint "[Hint qq87t] New theorem: `Tendsto.if`."
  apply Tendsto.if
  Hint "[Hint xcip8] Perfect.  Now you have cut the function in two halves, and have two goals.
    First, need to show that left half of function tends to `0` as `x → 0` “from the left”,
    i.e. along `𝓝[≤] 0`. Note that here the function is constant."
  Hint (hidden := true) "[Hint lpk2t] Remember `tendsto_const_nhds`."
  apply tendsto_const_nhds
  Hint "[Hint gh8td] Second, need to show that right half of function tends to `0` as `x → 0`
    “from the right”.
    But “from the right” is not written nicely.
    Change `¬ x ≤ 0` to `0 < x` using `not_le` or `simp`."
  simp
  Hint "[Hint 65tuz] Now the filter reads `𝓝[>] 0`.
    Next, pull the minus out of the `exp` using `simp_rw` and new theorem `exp_neg`."
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
    Hint "[Hint mbyuc] Exactly new theorem: `tendsto_inv_nhdsGT_zero`."
    apply tendsto_inv_nhdsGT_zero
  Hint (hidden := true) "[Hint 6bxi7] You're in good shap. Remember new theorem: `Tendsto.comp`."
  apply Tendsto.comp h1 h2

  /-
  Hint "[Hint sm4cgr] If `f₁` is eventually equal to `f₂` along a filter `l₁`, then `f₁` tending to
    `l₂` along `l₁` implies `f₂` does too. This is `Tendsto.congr'` in Mathlib."
  Hint (hidden := true) "[Hint sm4apc] Apply `Tendsto.congr' _ {this}`."
  apply Tendsto.congr' _ this
  -/

/---/
TheoremDoc Filter.Tendsto.if as "Tendsto.if" in "Filter"
/---/
TheoremDoc Filter.Tendsto.comp as "Tendsto.comp" in "Filter"
/---/
TheoremDoc Real.exp_neg as "exp_neg" in "Function"
/---/
TheoremDoc tendsto_inv_nhdsGT_zero as "tendsto_inv_nhdsGT_zero" in "Function"

NewTheorem Filter.Tendsto.if Filter.Tendsto.comp Real.exp_neg tendsto_inv_nhdsGT_zero
