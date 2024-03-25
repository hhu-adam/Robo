-- import Game.Metadata
import GameServer.Commands

import Game.Levels.MatrixTrace.L05_EqOnEBasisDiagSum
import Game.Levels.MatrixTrace.L08_OneOnDiagEBasis


World "Trace"
Level 1

Title "Trace"

Introduction
"
The trace as a map from the space of `n × n` matrices to the field of scalars has the following properties:
1. It is linear, witnessed by `traceLinear`.
2. The trace of a identity matrix is the dimension of the matrix, i.e.
`trace (1 : Matrix α α ℝ) = Fintype.card α`.
3. The matrices in the trace of a product can be switched without changing the result, i.e. `trace (A * B) = trace (B * A)`. This is witnessed by `trace_mul_comm`.

We show that these properties characterize the trace, that is any map satisfying these properties is equal to the trace.
"

open Nat Matrix BigOperators StdBasisMatrix Finset

set_option relaxedAutoImplicit false
set_option autoImplicit false

/- Statements about linear maps and sums. -/


#check mul_eq_mul_left_iff


/- The Statement -/

#check (![] : Matrix (Fin 0) (Fin 0) ℝ) = 0

-- example {n : ℕ} (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ) : ↑ f = f.toFun := rfl

Statement {n : ℕ} (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ)
    (h₁ : ∀ A B, f (A * B) = f (B * A)) (h₂ : f 1 = n) :
    trace = f := by
  ext A
  rw [eq_sum_apply_diag_ebasis (zero_on_offdiag_ebasis h₁)]
  rcases n
  · simp
  · simp_rw [eq_on_diag_ebasis h₁ _ 0]
    rw [← sum_mul]
    rw [one_on_diag_ebasis h₁ h₂ 0]
    simp [trace]
