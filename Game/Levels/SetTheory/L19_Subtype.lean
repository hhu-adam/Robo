import Game.Metadata
import Game.Levels.SetTheory.L18_SetOf


World "SetTheory2"
Level 6

Title ""

Introduction
"
"

open Set

/--  -/
Statement :
    3 ∈ {n : ℕ | Odd n} := by
  rw [mem_setOf]
  use 1
  ring

TheoremTab "Set"
