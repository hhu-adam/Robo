import Game.Levels.Smooth.L04
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

World "Smooth"
Level 8

open Polynomial Filter Topology

/-- The derivative of `x ↦ p(x⁻¹) · f x` keeps the same `polynomial · f` shape. -/
TheoremDoc hasDerivAt_polynomial_eval_inv_mul as "hasDerivAt_polynomial_eval_inv_mul" in "Function"

Statement hasDerivAt_polynomial_eval_inv_mul (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun x ↦ p.eval x⁻¹ * f x)
      ((X ^ 2 * (p - derivative p)).eval x⁻¹ * f x) x := by
  Hint "[Hint sm8lttri] First, try to use `lt_trichotomy` to divide into three cases."
  obtain hx | rfl | hx := lt_trichotomy x 0
  · rw [zero_of_nonpos hx.le, mul_zero]
    have : (fun (x : ℝ) ↦ eval x⁻¹ p * f x) =ᶠ[𝓝 x] fun _ ↦ 0 := by
      have : ∀ᶠ y in 𝓝 x, y < 0 := by
        apply eventually_lt_nhds hx
      filter_upwards [this]
      intro a ha
      rw [zero_of_nonpos ha.le, mul_zero]
    apply HasDerivAt.congr_of_eventuallyEq _ this
    apply hasDerivAt_const
  ·
    rw [zero_of_nonpos, mul_zero, hasDerivAt_iff_tendsto_slope]
    have aux {x : ℝ} : slope (fun (x : ℝ) ↦ eval x⁻¹ p * f x) 0 x = eval x⁻¹ (p * X) * f x := by
      simp [f, slope_def_field, div_eq_mul_inv, mul_right_comm]
    /- -- mathlib proof
    refine ((tendsto_polynomial_inv_mul_zero (p * X)).mono_left inf_le_left).congr fun x ↦ ?_
    simp [slope_def_field, div_eq_mul_inv, mul_right_comm]
    -/
    apply Tendsto.congr (fun x => aux.symm)
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    apply tendsto_polynomial_inv_mul_zero
    · grind
  · have hnot_le {y : ℝ} (hy : 0 < y) : ¬ y ≤ 0 := by grind
    Branch
      -- mathlib proof
      have := ((p.hasDerivAt x⁻¹).mul (hasDerivAt_neg _).exp).comp x (hasDerivAt_inv hx.ne')
      convert! this.congr_of_eventuallyEq _ using 1
      · simp [f, hnot_le hx]
        ring
      · filter_upwards [eventually_gt_nhds hx] with y hy
        simp [f, hnot_le hy]
    /- By definition, `f x = Real.exp (-x⁻¹)`, since `0 < x` -/
    have hf : f x = Real.exp (-x⁻¹) := by
      simp [f, hnot_le hx]
    have hev : (fun y ↦ eval y⁻¹ p * f y) =ᶠ[𝓝 x] fun y ↦ eval y⁻¹ p * Real.exp (-y⁻¹) := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      simp [f, hnot_le hy]
    have hp : HasDerivAt (fun y ↦ eval y p) (eval x⁻¹ (derivative p)) x⁻¹ := by
      apply p.hasDerivAt
    have hmul : HasDerivAt (fun y ↦ eval y p * Real.exp (-y))
        (eval x⁻¹ (derivative p) * Real.exp (-x⁻¹) +
          eval x⁻¹ p * (Real.exp (-x⁻¹) * -1)) x⁻¹ := by
      apply HasDerivAt.mul hp
      · apply HasDerivAt.exp
        apply hasDerivAt_neg
    have main : HasDerivAt (fun y ↦ eval y⁻¹ p * f y)
        ((eval x⁻¹ (derivative p) * Real.exp (-x⁻¹) +
          eval x⁻¹ p * (Real.exp (-x⁻¹) * -1)) * -(x ^ 2)⁻¹) x := by
      apply HasDerivAt.congr_of_eventuallyEq _ hev
      · apply hmul.comp x
        apply hasDerivAt_inv hx.ne'
    have hval : eval x⁻¹ (X ^ 2 * (p - derivative p)) * f x =
      (eval x⁻¹ (derivative p) * Real.exp (-x⁻¹) +
        eval x⁻¹ p * (Real.exp (-x⁻¹) * -1)) * -(x ^ 2)⁻¹ := by
      rw [hf]
      simp
      ring
    rw [hval]
    apply main

/---/
TheoremDoc Filter.Tendsto.congr as "Filter.Tendsto.congr"

/---/
TheoremDoc eventually_gt_nhds as "eventually_gt_nhds"

/---/
TheoremDoc mul_right_comm as "mul_right_comm"

NewTheorem Filter.Tendsto.congr MulZeroClass.mul_zero eventually_gt_nhds mul_right_comm
