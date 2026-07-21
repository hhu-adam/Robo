import Game.Levels.Smooth.L06
import Mathlib.Analysis.Calculus.Deriv.Basic

World "Smooth"
Level 7

open Real Filter Topology

Introduction "
Derivatives are *local*: if two functions agree on a whole neighbourhood of `a`,
they must have the same derivative at `a`. Mathlib packages this as
`HasDerivAt.congr_of_eventuallyEq`, where `f₁ =ᶠ[𝓝 a] f` reads “`f₁` and `f`
agree near `a`”.

In this level you differentiate the bump function `f` on the negative axis,
where it is flat: for `x < 0` it is constantly `0` nearby, so its derivative
is `0`.
"

/---/
TheoremDoc HasDerivAt.congr_of_eventuallyEq as "HasDerivAt.congr_of_eventuallyEq"

/---/
TheoremDoc hasDerivAt_const as "hasDerivAt_const"

/- For `x < 0`, the bump function `f` is eventually `0`, so its derivative is `0`. -/
Statement (x : ℝ) (hx : x < 0) : HasDerivAt f 0 x := by
  Hint "[Hint cev1] Near a negative point `f` is constantly `0`. So show `f`
    agrees with the zero function on a neighbourhood, then transport the
    constant's derivative with `HasDerivAt.congr_of_eventuallyEq`."
  Hint (hidden := true) "[Hint cev2] Build the local agreement first:
    `have h : f =ᶠ[𝓝 x] fun _ ↦ 0`. Points near `x` are still negative by
    `eventually_lt_nhds hx`, so `filter_upwards` and simplify `f`."
  have h : f =ᶠ[𝓝 x] fun _ ↦ 0 := by
    filter_upwards [eventually_lt_nhds hx] with y hy
    simp [f, hy.le]
  Hint (hidden := true) "[Hint cev3] Now `apply HasDerivAt.congr_of_eventuallyEq _ h`,
    then close the constant's derivative with `hasDerivAt_const`."
  apply HasDerivAt.congr_of_eventuallyEq _ h
  apply hasDerivAt_const

NewTheorem HasDerivAt.congr_of_eventuallyEq hasDerivAt_const
