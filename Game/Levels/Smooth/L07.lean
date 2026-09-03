import Game.Levels.Smooth.L06
import Mathlib.Analysis.Calculus.Deriv.Basic

World "Smooth"
Level 7

open Real Filter Topology STakeOff

Introduction "Intro Smooth L07"

/---/
TheoremDoc HasDerivAt.congr_of_eventuallyEq as "HasDerivAt.congr_of_eventuallyEq"

/---/
TheoremDoc hasDerivAt_const as "hasDerivAt_const"

/- For `x < 0`, the bump function `f` is eventually `0`, so its derivative is `0`. -/
Statement (x : ℝ) (hx : x < 0) : HasDerivAt f 0 x := by
  Hint "[Hint sm7bgf] In this level you differentiate the smooth take-off function `f` on the negative axis,
  where it is flat: for `x < 0` it is constantly `0` nearby, so its derivative
  is `0`."
  Hint "[Hint cev1] Note that if two function are eventually euqal around a point, then their derivatives agree
    at this point. The theorem is called `HasDerivAt.congr_of_eventuallyEq` in mathlib.
    First show `f` eventually equal to the zero function around `x`, then apply the theorem
    `HasDerivAt.congr_of_eventuallyEq`. "
  Hint (hidden := true) (strict := true) "[Hint cev2] Establish `f =ᶠ[𝓝 x] fun _ ↦ 0` by `have`"
  have h : f =ᶠ[𝓝 x] fun _ ↦ 0 := by
    Hint "[Hint sm7fu] Remember the theorem `eventually_lt_nhds`."
    Hint (hidden := true) "[Hint sm7fuh] Try to combine `filter_upwards` and `eventually_lt_nhds {hx}`."
    filter_upwards [eventually_lt_nhds hx] with y hy
    simp [f, hy.le]
  Hint (hidden := true) "[Hint cev3] Now `apply HasDerivAt.congr_of_eventuallyEq _ {h}`."
  apply HasDerivAt.congr_of_eventuallyEq _ h
  Hint (hidden := true) "Note that `hasDerivAt_const`."
  apply hasDerivAt_const

/-- For `h : a < b`, `h.le` is a short-cut of `a ≤ b`. -/
TheoremDoc LT.lt.le as "LT.lt.le" in "≤"

NewTheorem HasDerivAt.congr_of_eventuallyEq hasDerivAt_const LT.lt.le
