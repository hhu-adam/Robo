import Game.Levels.MatrixTrace.L01_SMulEBasis

World "Trace"
Level 2

Title "Matrix"

-- TODO: Do we need this level??

Introduction
"
The matrix `E i j` is defined as the matrix with a `1` at position `i, j` and `0` elsewhere. They are extemely sparse. In below, `E i j` are defined in terms of mathlib's `stdBasisMatrix`.

`stdBasisMatrix i j c` is the matrix with `c` at position `i, j` and `0` elsewhere. `stdBasisMatrix` matrices are closed under scalar multiplication, becasue
`c • stdBasisMatrix i j 1 = stdBasisMatrix i j c`, a theorem witnessed by `smul_stdBasisMatrix`.

"

open Nat Matrix BigOperators


-- @[inherit_doc Matrix.StdBasisMatrix.mul_of_ne]
Statement Matrix.E.mul_of_ne {n : ℕ} (i j : Fin n) {k l : Fin n} (h : j ≠ k) : E i j * E k l = 0 := by
  unfold E
  simp [h]

NewDefinition Matrix.E
TheoremTab "Matrix"
