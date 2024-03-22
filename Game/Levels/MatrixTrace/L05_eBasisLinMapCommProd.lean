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

lemma apply_ebasis_diag {n : ℕ} {f : Matrix (Fin n.succ) (Fin n.succ) ℝ →ₗ[ℝ] ℝ}
    (h : ∀ A B, f (A * B) = f (B * A)) (j : Fin n.succ) :
    f (E j j) = f (E 0 0) := by
  trans f (E j 0 * E 0 j)
  · rw [mul_same, mul_one]
  · rw [h, mul_same, mul_one]
