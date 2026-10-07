import Game.Levels.Cauchy.L11

World "Cauchy"
Level 12

open Polynomial Cauchy
open scoped ContDiff

Introduction "Intro Cauchy L12 (Second boss)"

Statement : ContDiff ℝ ∞ f := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro m h
  clear h
  rw [iteratedDeriv_eq_poly]
  intro x
  apply HasDerivAt.differentiableAt (hasDerivAt_polynomial_eval_inv_mul _ _)
