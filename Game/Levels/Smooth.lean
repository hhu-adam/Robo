import Game.Levels.Smooth.L01
import Game.Levels.Smooth.L02
import Game.Levels.Smooth.L03
import Game.Levels.Smooth.L04
import Game.Levels.Smooth.L05
import Game.Levels.Smooth.L06
import Game.Levels.Smooth.L07
import Game.Levels.Smooth.L08
import Game.Levels.Smooth.L09
import Game.Levels.Smooth.L10
import Game.Levels.Smooth.L11
import Game.Levels.Smooth.L12

/-!
The planet Smooth builds the smooth take-off function `f x = if x ≤ 0 then 0 else
exp (-x⁻¹)`: from polynomial evaluation and `exp` outgrowing polynomials, through
the derivative rules (`HasDerivAt.comp`, `.mul`, `.exp`, `hasDerivAt_inv`,
`hasDerivAt_neg`), up to the formula for every iterated derivative of `f` and
finally the fact that `f` is smooth (`ContDiff ℝ ∞ f`, via
`contDiff_of_differentiable_iteratedDeriv`).
-/

World "Smooth"
Title "Smooth"

Introduction "Intro Smooth"
