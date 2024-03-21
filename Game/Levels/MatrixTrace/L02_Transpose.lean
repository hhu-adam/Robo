--import Game.Metadata
import GameServer.Commands

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Trace

--import Game.StructInstWithHoles

set_option tactic.hygienic false

World "Trace"
Level 2

Title "Trace"

Introduction
"
The transpose of a matrix `A` is denoted `Aᵀ` and is defined to be the matrix whose `(i, j)`-th entry is the `(j, i)`-th entry of `A`:

```
(Aᵀ) i j = A j i
```
The trace of the transpose of a matrix is equal to the trace of the matrix itself.

In this level, we shall prove that the trace of the product of a matrix with its transpose is always non-negative.

"

open Matrix BigOperators

#synth Mul (Matrix (Fin 3) (Fin 3) ℝ)


lemma mul_tranpose_diag_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    diag (A * Aᵀ) i = ∑ k, (A i k)^2 := by
  simp only [transpose, pow_two]
  rfl

Statement {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ trace (A * Aᵀ) := by
  simp only [trace]
  simp only [transpose]
  simp only [diag]
  simp only [Matrix.mul_apply]
  simp only [of_apply]
  simp only [← pow_two] -- positivity fails! A bug? something to improve?
  positivity


-- Statement {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
--     0 ≤ trace (A * Aᵀ) := by
--   rw [trace]
--   rw [transpose]
--   simp_rw [diag]
--   simp_rw [Matrix.mul_apply]
--   simp_rw [of_apply]
--   simp_rw [← pow_two]
--   positivity
