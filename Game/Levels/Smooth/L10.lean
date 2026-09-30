import Game.Levels.Smooth.L09

World "Smooth"
Level 10

open Real
open scoped ContDiff

Introduction "Intro Smooth L10"

/---/
TheoremDoc contDiff_of_differentiable_iteratedDeriv as "contDiff_of_differentiable_iteratedDeriv"
  in "Function"

/---/
TheoremDoc HasDerivAt.differentiableAt as "HasDerivAt.differentiableAt" in "Function"

/---/
TheoremDoc Real.hasDerivAt_exp as "Real.hasDerivAt_exp" in "Function"

Statement : ContDiff ℝ ∞ exp := by
  Hint "[Hint sm10bgf] `ContDiff ℝ ∞` means *smooth*: differentiable arbitrarily often.
    By `contDiff_of_differentiable_iteratedDeriv` it suffices to show that every
    iterated derivative is differentiable. For `exp` this is easy, since every derivative of
    exp is exp itself."
  Hint (strict := true) (hidden := true) "[Hint sm10ih] First establish
    `∀ m, iteratedDeriv m exp = exp` by induction."
  have h : ∀ m, iteratedDeriv m exp = exp := by
    intro m
    induction m with n ih
    · apply iteratedDeriv_zero
    · funext x
      rw [iteratedDeriv_succ, ih]
      Hint (hidden := true) "[Hint sm10hd] Remember `HasDerivAt.deriv` and `Real.hasDerivAt_exp`."
      apply HasDerivAt.deriv
      apply Real.hasDerivAt_exp
  Hint (strict := true) "[Hint sm10cd] By `{h}`, every iterated derivative of `exp` is exp
    itself. A function is smooth as soon as all of its iterated derivatives are differentiable,
    so it only remains to see that exp is differentiable."
  Hint (hidden := true) "[Hint sm10df] Apply the theorem `contDiff_of_differentiable_iteratedDeriv`."
  apply contDiff_of_differentiable_iteratedDeriv
  intro m _
  rw [h]
  intro x
  Hint (hidden := true) "[Hint sm10da] Remember `HasDerivAt.differentiableAt` and `Real.hasDerivAt_exp`."
  apply HasDerivAt.differentiableAt (Real.hasDerivAt_exp _)

NewTheorem contDiff_of_differentiable_iteratedDeriv HasDerivAt.differentiableAt
  Real.hasDerivAt_exp

NewDefinition ContDiff
