import Game.Levels.Cauchy.L01
import Game.Levels.Cauchy.L02
import Game.Levels.Cauchy.L03
import Game.Levels.Cauchy.L04
import Game.Levels.Cauchy.L05
import Game.Levels.Cauchy.L06
import Game.Levels.Cauchy.L07
import Game.Levels.Cauchy.L08
import Game.Levels.Cauchy.L09
import Game.Levels.Cauchy.L10
import Game.Levels.Cauchy.L11
import Game.Levels.Cauchy.L12

/-!
The planet Cauchy builds the smooth take-off function `f x = if x ≤ 0 then 0 else
exp (-x⁻¹)`: from polynomial evaluation and `exp` outgrowing polynomials, through
the derivative rules (`HasDerivAt.comp`, `.mul`, `hasDerivtAt_exp`, `hasDerivAt_inv`,
`hasDerivAt_neg`), up to the formula for every iterated derivative of `f` and
finally the fact that `f` is smooth (`ContDiff ℝ ∞ f`, via
`contDiff_of_differentiable_iteratedDeriv`).
-/

World "Cauchy"
Title "Cauchy"

Introduction "Intro Cauchy"
