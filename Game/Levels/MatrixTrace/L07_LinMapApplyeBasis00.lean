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

-- H5
lemma apple_ebasis_00 {n : ℕ} {f : Matrix (Fin n.succ) (Fin n.succ) ℝ →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A)) (h₂ : f 1 = n.succ) :
    f (E 0 0) = 1 := by
  rcases H4' h₁ h₂
  · assumption
  · exfalso
    apply succ_ne_zero n
    rw [succ_eq_add_one]
    rw [← cast_zero] at h
    apply Nat.cast_injective at h
    assumption
