import Game.Levels.Smooth.L03
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Inv
-- import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

World "Smooth"
Level 4

open Polynomial Filter Topology

lemma zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : f x = 0 := by
  simp_log [f, hx]

Statement hasDerivAt_polynomial_eval_inv_mul (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun x ↦ p.eval x⁻¹ * f x)
      ((X ^ 2 * (p - derivative (R := ℝ) p)).eval x⁻¹ * f x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
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
    rw [zero_of_nonpos (le_refl 0), mul_zero, hasDerivAt_iff_tendsto_slope]
    have aux {x : ℝ} : slope (fun (x : ℝ) ↦ eval x⁻¹ p * f x) 0 x = eval x⁻¹ (p * X) * f x  := by
      simp_log [f, slope_def_field, div_eq_mul_inv, mul_right_comm]
    Branch
      -- mathlib proof
      refine ((tendsto_polynomial_inv_mul_zero (p * X)).mono_left inf_le_left).congr fun x ↦ ?_
      simp [slope_def_field, div_eq_mul_inv, mul_right_comm]
    apply Tendsto.congr (fun x => aux.symm)
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    apply tendsto_polynomial_inv_mul_zero
  ·

    Branch
      have := ((p.hasDerivAt x⁻¹).mul (hasDerivAt_neg _).exp).comp x (hasDerivAt_inv hx.ne')
      convert! this.congr_of_eventuallyEq _ using 1
      · simp_log [f, hx.not_ge]
        ring
      · filter_upwards [lt_mem_nhds hx] with y hy
        simp_log [f, hy.not_ge]
    sorry
    -- rw [zero_of_nonpos hx.le, mul_zero]
    -- refine (hasDerivAt_const _ 0).congr_of_eventuallyEq ?_
