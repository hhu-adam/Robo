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

Statement (x : ℝ) (hx : x < 0) : HasDerivAt f 0 x := by
  Hint "[Hint sm7bgf] In this level you differentiate the smooth take-off function `f` on the
    negative axis, where it is flat: around `x < 0` it is constantly `0`, so its derivative is `0`.

    Note that if two functions are eventually euqal around a point, then their derivatives agree
    at this point. This theorem is called `HasDerivAt.congr_of_eventuallyEq`.
    So show first f is eventually equal to the zero function around `x`."
  Hint (hidden := true) (strict := true) "[Hint cev2] Establish `f =ᶠ[𝓝 x] fun _ ↦ 0`."
  have h : f =ᶠ[𝓝 x] fun _ ↦ 0 := by
    Hint "[Hint sm7fu] Remember `eventually_lt_nhds` and `filter_upwards`."
    Hint (hidden := true) "[Hint sm7fuh] First, establish `hy : ∀ᶠ (y : ℝ) in 𝓝 x, y < 0`.
      Then use `filter_upwards` with `hy`."
    have hy := eventually_lt_nhds hx
    filter_upwards [hy]
    intro a ha
    simp [f]
    grind
  Hint (strict := true) "[Hint cev3] The constant function has derivative zero at any `x`:
    establish this using `hasDerivAt_const (x : ℝ) (0 : ℝ)`."
  have h_const := hasDerivAt_const (x : ℝ) (0 : ℝ)
  Hint (hidden := true) "[Hint y4ym4] Finally time to apply `HasDerivAt.congr_of_eventuallyEq`."
  apply HasDerivAt.congr_of_eventuallyEq h_const h

NewTheorem HasDerivAt.congr_of_eventuallyEq hasDerivAt_const
