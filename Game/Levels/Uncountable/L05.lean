import Game.Metadata
import Mathlib.Data.Rat.Encodable

World "Uncountable"
Level 5

noncomputable section

open Function Cardinal

Statement : #ℚ = ℵ₀ := by
  Hint "[Hint mkQ] Remember we have just prove that `ℚ` is countable."
  apply Cardinal.mk_eq_aleph0

/---/
TheoremDoc Cardinal.mk_eq_aleph0 as "Cardinal.mk_eq_aleph0" in "Cardinal"

NewTheorem Cardinal.mk_eq_aleph0
