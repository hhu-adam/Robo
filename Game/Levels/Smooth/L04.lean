import Game.Levels.Smooth.L03
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.PolynomialExp

World "Smooth"
Level 4

open Real Filter Topology

Introduction "
Because `exp` outgrows every polynomial (level 2), the take-off function `f`
crushes any polynomial factor to `0` as `x → 0`: even multiplied by `p.eval x⁻¹`,
which blows up, the product still tends to `0`.
"

/-- -/
Statement tendsto_polynomial_inv_mul_zero (p : Polynomial ℝ) :
    Tendsto (fun x ↦ p.eval x⁻¹ * f x) (𝓝 0) (𝓝 0) := by
  simp [f]
  apply tendsto_const_nhds.if
  simp
  have tendsto_top : Tendsto (fun (x : ℝ) ↦ x⁻¹) (𝓝[>] 0) atTop := by
    apply tendsto_inv_nhdsGT_zero
  have : Tendsto (fun x ↦ p.eval x⁻¹ / exp x⁻¹) (𝓝[>] 0) (𝓝 0) := by
    apply p.tendsto_div_exp_atTop.comp
    apply tendsto_top
  Branch
    -- mathlib proof
    refine this.congr' <| mem_of_superset self_mem_nhdsWithin fun x hx ↦ ?_
    simp [exp_neg, div_eq_mul_inv]
  apply this.congr'
  filter_upwards
  simp [exp_neg, div_eq_mul_inv]
