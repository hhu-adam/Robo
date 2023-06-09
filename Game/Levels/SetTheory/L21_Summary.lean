import Game.Metadata

import Game.Options.MathlibPart

World "SetTheory"
Level 21

Title ""

Introduction
"
"

open Set

Statement
"" :
    3 ∈ {n : ℕ | Odd n}  := by
  rw [mem_setOf]
  use 1
  ring

NewTactic constructor intro rw assumption rcases simp tauto trivial
LemmaTab "Set"
