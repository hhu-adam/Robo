import Game.Metadata


World "Mono"
Level 2

Title ""

Introduction
""

open Function

Statement (f : ℤ → ℤ  ) (hf : Injective f): f 1 ≠ f (-1) := by
  rw [Injective.ne_iff]
  decide
  assumption

/---/
TheoremDoc Function.Injective.ne_iff as "Injective.ne_iff" in "Function"
NewTheorem Function.Injective.ne_iff
