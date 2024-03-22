--import Game.Metadata
import GameServer.Commands

import Game.Levels.MatrixTrace.L03_eBasisSpan

--import Game.StructInstWithHoles

set_option tactic.hygienic false

World "Trace"
Level 5

Title "Trace"

Introduction
"
The commutator of two matrices is defined as the difference between their product and the product
of the matrices in the opposite order, that is the commutator of `A` and `B` is `A * B - B * A`.
A linear functional `f` on the space of `n × n` matrices which kills all commutators has the same value on all the diagonal elemantary basis matrices, i.e. `f (E i i) = f (E j j)` for all `i` and `j`.
"

open Nat Matrix BigOperators StdBasisMatrix

-- H1
lemma apply_ebasis_diag {n : ℕ} {f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ}
    (h : ∀ A B, f (A * B) = f (B * A))  :
    ∀ (i j : Fin n), f (E i i) = f (E j j) := by
  intro i j
  trans f (E i j * E j i)
  · rw [mul_same, mul_one]
  · rw [h, mul_same, mul_one]
