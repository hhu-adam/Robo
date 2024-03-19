--import Game.Metadata
import GameServer.Commands

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.RowCol


import Game.StructInstWithHoles

set_option tactic.hygienic false

World "Matrix"
Level 1

Title "Matrix"

Introduction
"
We can see a `n`-dimensional vector in two ways as a matrix:
- as a `1 × n` matrix whose only row consists of the components of the vector. This is the so-called row matrix of the vector: Given a vector `u : (Fin n) → ℝ`, we define a matrix `Matrix.row u : Matrix 1 n ℝ` by `M 0 j = u j`.

 an `n × 1` matrix whose only column consists of the components of the vector. This is the so-called column matrix of the vector: Given a vector `v : (Fin n) → ℝ`, we define a matrix `Matrix.col v : Matrix n 1 ℝ` by `M i 0 = v i`.
"

open Matrix

example : Fin 1 ≃ Unit := by exact finOneEquiv

example (e : α ≃ β) (f : α → γ) : β → γ := fun b => f <| e.invFun <| b

#check Equiv

#check ![(1 : ℝ) , 1]
#check !![(1 : ℝ) , 1]

example : Matrix.row ![1, 1] = !![1, 1] := sorry -- should we override Mathlib's definition of `.row` and `.columns`? Or we can cast matrices across the equivalence finOneEquiv -- check `TransferInstance` and `reindex`

/-- `Matrix.row u` is the row matrix whose entries are given by `u`. -/
@[simp]
def rowMatrix (u : Fin n → α) : Matrix (Fin 1) (Fin n) α :=
  fun _ j => u j

/-- `Matrix.col v` is the column matrix whose entries are given by `v`. -/
@[simp]
def colMatrix (v : Fin m → α) : Matrix (Fin m) (Fin 1) α :=
  fun i _ => v i

example : rowMatrix ![1, 1] = !![1, 1] := by
  funext i j
  simp only [rowMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]


-- Relate the row matrix and column matrix as transposition
example {u v : ℝ} : (rowMatrix ![u, v])ᵀ = colMatrix ![u, v] := by
  funext i _
  simp only [transpose_apply, rowMatrix, colMatrix]
