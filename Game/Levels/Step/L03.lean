import Game.Metadata


World "Step"
Level 3

/- # Introduction

Besides adding vectors, we can *scale* them.  For a scalar `a : ℝ` and a vector
`v : Fin n → ℝ`, the scalar multiple `a • v` is again a vector, defined coordinatewise by
`(a • v) i = a * v i`.

The symbol `•` is written `\smul`.  Combined with addition, scaling lets us form
*linear combinations* such as `a • v + b • w`, the central object of this world.

-/

open Real Function Set Finset

Statement :
    sqrt 2 • ![(sqrt 2)/2, 0] + sqrt 2 • ![0, (sqrt 2)/2] = ![1, 1] := by
  simp
  ring
  simp

TheoremTab "LinearAlgebra"
