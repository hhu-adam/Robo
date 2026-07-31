import Game.Levels.Smooth.L04
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

World "Smooth"
Level 8

Introduction "Intro Smooth L08:
In this level, you are going to prove that the derivative of $p(x^{-1}) f(x)$ is
  $x^{-2} (p(x) - p'(x)) f (x)$, where
  $$
f(x) = \\begin{cases} 0 & \\text{if } x \\le 0, \\\\ e^{-1/x} & \\text{if } x > 0. \\end{cases}
$$"

open Polynomial Filter Topology

/-- The derivative of `x ↦ p(x⁻¹) · f x` keeps the same `polynomial · f` shape. -/
TheoremDoc hasDerivAt_polynomial_eval_inv_mul as "hasDerivAt_polynomial_eval_inv_mul" in "Function"

Statement hasDerivAt_polynomial_eval_inv_mul (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun x ↦ p.eval x⁻¹ * f x)
      ((X ^ 2 * (p - derivative p)).eval x⁻¹ * f x) x := by
  Hint "[Hint sm8lttri] First, try to use `lt_trichotomy` to divide into three cases."
  obtain hx | rfl | hx := lt_trichotomy x 0
  · Hint "[Hint s8ls0] This is a similar case of the previous level. Recall the method you
      use in the previous level."
    rw [zero_of_nonpos hx.le, mul_zero]
    Hint (strict := true) "[Hint s8l0] Note that the function `p.eval i⁻¹ * f i` eventually equals to zero
      around `x`."
    Hint (strict := true) (hidden := true) "[Hint sm8hdl] Establish
      `(fun (i : ℝ) ↦ p.eval i⁻¹ * f i) =ᶠ[𝓝 x] fun _ ↦ 0` by `have`."
    have he : (fun (i : ℝ) ↦ p.eval i⁻¹ * f i) =ᶠ[𝓝 x] fun _ ↦ 0 := by
      Hint (hidden := true) "[Hint s8fuelhx] Combine `filter_upwards` and `eventually_lt_nhds`."
      filter_upwards [eventually_lt_nhds hx]
      intro a ha
      rw [zero_of_nonpos ha.le, mul_zero]
    Hint (hidden := true) "[Hint s8rcoe] Remember the theorem `HasDerivAt.congr_of_eventuallyEq`."
    apply HasDerivAt.congr_of_eventuallyEq _ he
    apply hasDerivAt_const
  · Hint "[Hint s8snmz] Note that `f 0 = 0`, then we could `rw` the goal using `zero_of_nonpos` and `mul_zero`."
    rw [zero_of_nonpos, mul_zero]
    Hint "[Hint s8rmhits] Remember the theorem `hasDerivAt_iff_tendsto_slope`."
    rw [hasDerivAt_iff_tendsto_slope]
    Hint (strict := true) "[Hint sm8sle] Note that the slope of function $p(x⁻¹)f (x)$
      between `0` and `y` is $(p * X)(y ⁻¹)f(y)$."
    Hint (strict := true) (hidden := true) "[Hint sm8sleh]
      Establish `∀ y, (p * X).eval y⁻¹ * f y = slope (fun (x : ℝ) ↦ p.eval x⁻¹ * f x) 0 y` by `have`."
    have aux : ∀ y, (p * X).eval y⁻¹ * f y = slope (fun (x : ℝ) ↦ p.eval x⁻¹ * f x) 0 y := by
      simp [f, slope_def_field]
      grind
    /- -- mathlib proof
    refine ((tendsto_polynomial_inv_mul_zero (p * X)).mono_left inf_le_left).congr fun x ↦ ?_
    simp [slope_def_field, div_eq_mul_inv, mul_right_comm]
    -/
    Hint "[Hint sm8rmtc] Remember the theorem `Filter.Tendsto.congr` and `{aux}`."
    apply Tendsto.congr aux
    Hint "[Hint sm9tlshf] It suffices to prove that the expression tends to `0` in the full neighborhood of `0`,
      not just the punctured neighborhood. Also remember the result you proved in the
      previous level `tendsto_polynomial_inv_mul_zero`."
    Branch
      suffices h : Tendsto (fun (x : ℝ) ↦ eval x⁻¹ (p * X) * f x) (𝓝 0) (𝓝 0)
      Hint (hidden := true) "[Hint sm8tlshf] Now apply `Tendsto.mono_left h nhdsWithin_le_nhds `."
      apply Tendsto.mono_left h nhdsWithin_le_nhds
      Hint "[Hint sm8tshiw] This is exactly the result `tendsto_polynomial_inv_mul_zero`."
      apply tendsto_polynomial_inv_mul_zero
    Hint (hidden := true) "[Hint sm8tmlst] Remember the theorem `Tendsto.mono_left` and `nhdsWithin_le_nhds`."
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    Hint "[Hint sm8tshiw] This is exactly the result `tendsto_polynomial_inv_mul_zero`."
    apply tendsto_polynomial_inv_mul_zero
    · grind
  ·
    /- -- mathlib proof
    have := ((p.hasDerivAt x⁻¹).mul (hasDerivAt_neg _).exp).comp x (hasDerivAt_inv hx.ne')
    convert! this.congr_of_eventuallyEq _ using 1
    · simp [f, hnot_le hx]
      ring
    · filter_upwards [eventually_gt_nhds hx] with y hy
      simp [f, hnot_le hy]
    -/
    /- By definition, `f x = Real.exp (-x⁻¹)`, since `0 < x` -/
    Hint (strict := true) "[Hint sm8hf] First establish that `f x = Real.exp (-x⁻¹)` by `have`."
    have hf : f x = Real.exp (-x⁻¹) := by
      unfold f
      rw [if_neg]
      grind
    Hint (strict := true) "[Hint sm8hevs] Perfect! Now you can also prove that
      `(fun y ↦ eval y⁻¹ p * f y) =ᶠ[𝓝 x] fun y ↦ eval y⁻¹ p * Real.exp (-y⁻¹)` by `have`."
    have hev : (fun y ↦ eval y⁻¹ p * f y) =ᶠ[𝓝 x] fun y ↦ eval y⁻¹ p * Real.exp (-y⁻¹) := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      unfold f
      rw [if_neg]
      grind
    Hint (strict := true) "[Hint sm8hval] Reordering the derivative to meet the form of
      `HasDerivAt.mul`."
    Hint (strict := true) (hidden := true) "[Hint sm8hvalh]
      Establish `eval x⁻¹ (X ^ 2 * (p - derivative p)) * f x =
      (eval x⁻¹ (derivative p) * Real.exp (-x⁻¹) +
        eval x⁻¹ p * (Real.exp (-x⁻¹) * -1)) * -(x ^ 2)⁻¹` by `have`."
    have hval : eval x⁻¹ (X ^ 2 * (p - derivative p)) * f x =
      (eval x⁻¹ (derivative p) * Real.exp (-x⁻¹) +
        eval x⁻¹ p * (Real.exp (-x⁻¹) * -1)) * -(x ^ 2)⁻¹ := by
      rw [hf]
      simp
      ring
    Hint (strict := true) "[Hint sm8gtrh] Perfect! You're on track. Now you can `rw` the expression
      using `hval`."
    rw [hval]
    Hint "[Hint sm8hcehev] Remember that the theorem `HasDerivAt.congr_of_eventuallyEq` and `{hev}`."
    apply HasDerivAt.congr_of_eventuallyEq _ hev
    Branch
      -- alternative proof
      have hmul : HasDerivAt (fun y ↦ eval y p * Real.exp (-y))
        (eval x⁻¹ (derivative p) * Real.exp (-x⁻¹) +
            eval x⁻¹ p * (Real.exp (-x⁻¹) * -1)) x⁻¹ := by
        apply HasDerivAt.mul (p.hasDerivAt _)
        · apply HasDerivAt.exp
          apply hasDerivAt_neg
      apply HasDerivAt.comp x hmul
      apply hasDerivAt_inv hx.ne'
    Hint (strict := true) (hidden := true) "Establish `(fun (y : ℝ) ↦ eval y⁻¹ p * Real.exp (-y⁻¹)) =
        (fun y ↦ p.eval y * Real.exp (-y)) ∘ (fun y ↦ y⁻¹)` by `have`."
    have comp_aux : (fun (y : ℝ) ↦ eval y⁻¹ p * Real.exp (-y⁻¹)) =
        (fun y ↦ p.eval y * Real.exp (-y)) ∘ (fun y ↦ y⁻¹) := by
      rfl
    Hint "[Hint sm8cmpaux] Now `rw` using `{comp_aux}`, then this is a situation you met before. Remember
    the theorem `HasDerivAt.comp`."
    rw [comp_aux]
    apply HasDerivAt.comp x
    · Hint (hidden := true) "[Hint sm8rmhm] Remember the theorem `HasDerivAt.mul`."
      apply HasDerivAt.mul
      · apply p.hasDerivAt
        /- here is the same situation in level 6.-/
      · apply HasDerivAt.exp
        apply hasDerivAt_neg
    apply hasDerivAt_inv
    grind



/---/
TheoremDoc eventually_gt_nhds as "eventually_gt_nhds"

/---/
TheoremDoc MulZeroClass.mul_zero as "mul_zero" in "+ *"

NewTheorem MulZeroClass.mul_zero eventually_gt_nhds
