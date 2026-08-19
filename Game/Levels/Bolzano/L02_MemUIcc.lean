import Game.Levels.Bolzano.L01_MaxOnIcc

World "Bolzano"
Level 2

Introduction "Intro Bolzano L02"

open Set FullGrind

/-- Anything lying between `a` and `b` belongs to the unordered interval `uIcc a b`. -/
TheoremDoc mem_uIcc_of_le_of_le as "mem_uIcc_of_le_of_le" in "Bolzano"

Statement mem_uIcc_of_le_of_le {a b y : ℝ} (h₁ : a ≤ y) (h₂ : y ≤ b) : y ∈ uIcc a b := by
  rw [Set.mem_uIcc]
  grind

NewTheorem Set.mem_uIcc

TheoremTab "Bolzano"
