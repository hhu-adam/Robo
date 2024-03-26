--import Game.Metadata
import GameServer.Commands

import Game.Levels.MatrixTrace.L01_VectorSpace

--import Game.StructInstWithHoles

set_option tactic.hygienic false

World "Matrix"
Level 6

Title "Matrix"

Introduction
"
The trace of a square matrix is the sum of the elements on its main diagonal. It is a linear map from the space of square matrices to the field of scalars. The lineariry is witnessed by the term `traceLinearMap` in Mathlib.

In Mathlib, trace is defined as the sum of the entries in the diagonal vector of a matrix:

```
∑ i, diag A i
```

where `diag A i = A i i`. You can prove `trace A = ∑ i, A i i` by `rfl`.

The trace of a identity matrix is the dimension of the matrix:

```
trace_one : trace (1 : Matrix α α ℝ) = Fintype.card α
```

Since `Fin n` has `n` elements, we have:

```
trace (1 : Matrix (Fin n) (Fin n) ℝ) = n
```

Use `trace_add` and `trace_sub` are special cases of the linearity of the trace which state that the trace of the sum of two matrices is the sum of their traces, and the trace of the difference of two matrices is the difference of their traces.

"

open Matrix BigOperators

Statement {n : ℕ} {t : ℝ} (A : Matrix (Fin n) (Fin n) ℝ) :
    trace (A - t • 1) = trace A - t * n := by
  rw [trace_sub]
  rw [trace_smul]
  rw [trace_one]
  rw [Fintype.card_fin]
  rfl

NewTheorem Fintype.card_fin Matrix.trace_one Matrix.trace_smul Matrix.trace_sub
