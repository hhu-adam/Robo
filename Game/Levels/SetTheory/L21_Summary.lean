import Game.Metadata



World "SetTheory"
Level 21

Title ""

Introduction
"
"

open Set

/--  -/
Statement :
    3 ∈ {n : ℕ | Odd n}  := by
  rw [mem_setOf]
  use 1
  ring

TheoremTab "Set"
