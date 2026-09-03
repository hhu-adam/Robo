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

/-!
The planet Smooth builds the smooth take-off function `f x = if x ≤ 0 then 0 else
exp (-x⁻¹)`: from polynomial evaluation and `exp` outgrowing polynomials, through
the derivative rules (`HasDerivAt.comp`, `.mul`, `.exp`, `hasDerivAt_inv`,
`hasDerivAt_neg`), up to the key fact that every iterated derivative of `f`
vanishes at `0` — so `f` is infinitely flat there.
-/

World "Smooth"
Title "Smooth"

Introduction "Intro Smooth"
