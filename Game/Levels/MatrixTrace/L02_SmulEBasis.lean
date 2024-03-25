-- import Game.Metadata
import GameServer.Commands

import Game.Levels.MatrixTrace.L01_VectorSpace

World "Trace"
Level 2

Title "Trace"

Introduction
"
The matrix `E i j` is defined as the matrix with a `1` at position `i, j` and `0` elsewhere. They are extemely sparse. In below, `E i j` are defined in terms of mathlib's `stdBasisMatrix`.

`stdBasisMatrix i j c` is the matrix with `c` at position `i, j` and `0` elsewhere. Note that the collection of `stdBasisMatrix` matrices are closed under scalar multiplication, becasue `c • stdBasisMatrix i j 1 = stdBasisMatrix i j c`, witnessed by `smul_stdBasisMatrix`.

"

open Nat Matrix BigOperators StdBasisMatrix

-- abbrev E {n : ℕ} (i j : Fin n) {R : Type*} [Semiring R] : Matrix (Fin n) (Fin n) R :=
--   stdBasisMatrix i j 1

abbrev E {n : ℕ} (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  stdBasisMatrix i j 1

lemma smul_ebasis {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j) : A i j • E i j = stdBasisMatrix i j (A i j) := by
  simp only [smul_stdBasisMatrix]
  simp only [smul_eq_mul, mul_one]
