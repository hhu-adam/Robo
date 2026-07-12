import Game.Metadata
import Mathlib.Data.Rat.Encodable

World "Uncountable"
Level 4

noncomputable section

open Function Cardinal

Statement : Countable ℚ := by
  infer_instance

-- TODO: add TacticDoc for `infer_instance`
/-- -/
TacticDoc infer_instance

NewTactic infer_instance
