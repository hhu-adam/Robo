import Game.Metadata

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

World "Span"
Level 3

Title "Span"

/- # Introduction

Since vectors are functions, we define their scalar multiplication pointwise.

-/

open Real Function Set Finset BigOperators

Statement : sqrt 2 • ![(sqrt 2)/2, 0] + sqrt 2 • ![0, (sqrt 2)/2] = ![1, 1] := by
  simp
  ring
  --norm_num
  simp
