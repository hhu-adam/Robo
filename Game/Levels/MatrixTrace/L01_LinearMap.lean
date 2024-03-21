--import Game.Metadata
import GameServer.Commands

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Trace

--import Game.StructInstWithHoles

set_option tactic.hygienic false

World "Trace"
Level 1

Title "Trace"

Introduction
"
The trace of a square matrix is the sum of the elements on its main diagonal. It is a linear map from the space of square matrices to the field of scalars. The lineariry is witnessed by the term `traceLinearMap` in Mathlib.

In Mathlib, trace is defined as the sum of the entries in the diagonal vector of a matrix:

```
∑ i, diag A i
```

where `diag A i = A i i`.

The trace of a identity matrix is the dimension of the matrix:
```
trace (1 : Matrix α α ℝ) = Fintype.card α
```

Since `Fin n` has `n` elements, we have:

```
trace (1 : Matrix (Fin n) (Fin n) ℝ) = n
```

Use `trace_add` or `trace_sub`, special cases of the linearity of the trace, to prove the following lemma:

```
trace (A - t 1) = trace A - t * n

```
where `t` is a scalar and `1` is the identity matrix of size `n`.

"

open Matrix BigOperators

lemma trace_eq_sum_diagonal_entries {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : trace A = ∑ i, A i i := rfl

lemma trace_one' : trace (1 :  Matrix (Fin n) (Fin n) ℝ) = n := by
  rw [trace_one]
  rw [Fintype.card_fin]

Statement {n : ℕ} {t : ℝ} (A : Matrix (Fin n) (Fin n) ℝ) :
    trace (A - t • 1) = trace A - t * n := by
  rw [trace_sub]
  rw [trace_smul]
  rw [trace_one]
  rw [Fintype.card_fin]
  rfl -- or `rw [smul_eq_mul]`
