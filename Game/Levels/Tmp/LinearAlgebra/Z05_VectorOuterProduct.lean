--import Game.Metadata
import GameServer.Commands

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation

import Game.Levels.Tmp.LinearAlgebra.Z01_Vector


--import Game.StructInstWithHoles

set_option tactic.hygienic false

open Matrix BigOperators

World "Matrix"
Level 2

Title "Matrix"

Introduction
"
The outer product of two vectors is a matrix.
"

def outerProduct [Mul α] (u : Fin m → α) (w : Fin n → α) : Matrix (Fin m) (Fin n) α :=
  fun i j => u i * w j


example : outerProduct ![(1 : ℝ),1] ![1,1] = !![1,1;1,1] := by
  sorry


-- Show that

open Matrix BigOperators
