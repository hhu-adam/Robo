import Game.Metadata

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

World "Span"
Level 2

Title "Span"

/- # Introduction

Since vectors are functions, we define their addition pointwise.

-/

open Real Function Set Finset BigOperators

Statement : ![(sqrt 3)/2, 1/2] + ![-(sqrt 3)/2, 1/2] = ![0, 1] := by
  Branch
    simp
    ring
  funext i
  fin_cases i <;>
  simp <;>
  ring
