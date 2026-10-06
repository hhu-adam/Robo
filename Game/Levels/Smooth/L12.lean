import Game.Levels.Smooth.L11

World "Smooth"
Level 12

open Polynomial STakeOff
open scoped ContDiff

Introduction "Intro Smooth L12"

Statement : ContDiff ℝ ∞ f := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro m h
  clear h
  rw [iteratedDeriv_eq_poly]
  intro x
  apply HasDerivAt.differentiableAt (hasDerivAt_polynomial_eval_inv_mul _ _)
