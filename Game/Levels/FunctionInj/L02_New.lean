import Game.Metadata


World "FunctionInj"
Level 2

Title "Preimage of surjective is injective"

Introduction
""

open Function

Statement (f : ℤ → ℤ  ) (hf : Injective f): f 1 ≠ f (-1) := by
  rw [Injective.ne_iff]
  decide
  assumption

NewTheorem Function.Injective.ne_iff
