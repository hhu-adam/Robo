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

"

open Nat Matrix BigOperators StdBasisMatrix

-- H2
lemma apply_ebasis_off_diag {n : ℕ} {f : Matrix (Fin n.succ) (Fin n.succ) ℝ →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A)) :
    ∀ (i j : Fin (n + 1)), (i ≠ j) → f (E i j) = 0 := by
  intro i j hne
  trans f (E i 0 * E 0 j)
  · rw [mul_same, mul_one]
  · rw [h₁]
    rw [mul_of_ne 0 j 1 hne.symm 1]
    simp
