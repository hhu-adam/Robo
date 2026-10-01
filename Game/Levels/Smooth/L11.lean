import Game.Levels.Smooth.L10

World "Smooth"
Level 11

open Polynomial STakeOff
open scoped ContDiff

Introduction "Intro Smooth L11 (Boss)"

Statement : ContDiff ℝ ∞ f := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro m _
  rw [iteratedDeriv_eq_poly]
  intro x
  apply HasDerivAt.differentiableAt (hasDerivAt_polynomial_eval_inv_mul _ _)
