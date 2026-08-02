import Game.Metadata
import Mathlib.Data.Rat.Encodable

World "Uncountable"
Level 4

noncomputable section

open Function Cardinal

Statement : #ℚ = ℵ₀ := by
  have hcQ : Countable ℚ := by
    apply instCountableRat
  Hint "[Hint mkQ] `ℚ` is countable and infinite — that is all `Cardinal.mk_eq_aleph0`
    needs."
  apply Cardinal.mk_eq_aleph0

/---/
TheoremDoc Cardinal.mk_eq_aleph0 as "Cardinal.mk_eq_aleph0" in "Cardinal"

/-- A type is countable if it can be enumerated by the natural numbers. -/
DefinitionDoc Countable as "Countable" in "Cardinal"

NewTheorem Cardinal.mk_eq_aleph0

NewDefinition Countable
