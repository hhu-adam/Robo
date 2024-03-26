--import Game.Metadata
import GameServer.Commands

import Game.Levels.MatrixTrace.L03_EBasisSpan

--import Game.StructInstWithHoles

set_option tactic.hygienic false

World "Matrix"
Level 9

Title "Matrix"

Introduction
"
In this level, we will show that a linear functional `f` on the space of matrices which kills all commutators also kills all off-diagonal elementary basis matrices.
"

open Nat Matrix BigOperators StdBasisMatrix

-- H2
Statement zero_on_offdiag_ebasis {n : ℕ} {f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A)) :
    ∀ (i j : Fin n ), (i ≠ j) → f (E i j) = 0 := by
  intro i j hne
  trans f (E i j * E j j)
  · rw [mul_same, mul_one]
  · rw [h₁]
    rw [mul_of_ne j j 1 hne.symm 1]
    simp
