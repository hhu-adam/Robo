-- import Game.Metadata
import GameServer.Commands

import Game.Levels.MatrixTrace.L01_VectorSpace

World "Matrix"
Level 4

Title "Matrix"

Introduction
"
The matrix `E i j` is defined as the matrix with a `1` at position `i, j` and `0` elsewhere. They are extemely sparse. In below, `E i j` are defined in terms of mathlib's `stdBasisMatrix`.

`stdBasisMatrix i j c` is the matrix with `c` at position `i, j` and `0` elsewhere.  `stdBasisMatrix` matrices are closed under scalar multiplication, becasue
`c • stdBasisMatrix i j 1 = stdBasisMatrix i j c`, a theorem witnessed by `smul_stdBasisMatrix`.

"

open Nat Matrix BigOperators StdBasisMatrix

abbrev E {n : ℕ} (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  stdBasisMatrix i j 1

Statement smul_ebasis {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j) : A i j • E i j = stdBasisMatrix i j (A i j) := by
  simp only [smul_stdBasisMatrix]
  simp only [smul_eq_mul, mul_one]

NewTheorem Matrix.smul_stdBasisMatrix mul_one smul_eq_mul smul_ebasis
