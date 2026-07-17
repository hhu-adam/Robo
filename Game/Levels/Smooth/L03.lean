import Game.Metadata
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.PolynomialExp

World "Smooth"
Level 3

open Real Filter Topology

noncomputable section

/-- Smooth take-off function -/
def f : ℝ → ℝ := fun x ↦ if x ≤ 0 then 0 else exp (- x⁻¹)

Statement tendsto_polynomial_inv_mul_zero (p : Polynomial ℝ) :
    Tendsto (fun x ↦ p.eval x⁻¹ * f x) (𝓝 0) (𝓝 0) := by
  simp_log [f]
  apply tendsto_const_nhds.if
  simp_log
  have tendsto_top : Tendsto (fun (x : ℝ) ↦ x⁻¹) (𝓝[>] 0) atTop := by
    apply tendsto_inv_nhdsGT_zero
  have : Tendsto (fun x ↦ p.eval x⁻¹ / exp x⁻¹) (𝓝[>] 0) (𝓝 0) := by
    apply p.tendsto_div_exp_atTop.comp
    apply tendsto_top
  Branch
    -- mathlib proof
    refine this.congr' <| mem_of_superset self_mem_nhdsWithin fun x hx ↦ ?_
    simp_log [exp_neg, div_eq_mul_inv]
  apply this.congr'
  filter_upwards
  simp_log [exp_neg, div_eq_mul_inv]
