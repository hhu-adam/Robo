import Game.Metadata
import Mathlib.Data.Rat.Encodable

World "Uncountable"
Level 4

Introduction "Intro Uncountable L04"

noncomputable section

open Function Cardinal

Statement : #ℚ = ℵ₀ := by
  have hcQ : Countable ℚ := by
    Hint "[Hint cQrat] Mathlib already knows that `ℚ` is countable: the instance
      `instCountableRat`."
    apply instCountableRat
  Hint "[Hint mkQ] `ℚ` is countable and infinite — that is all `Cardinal.mk_eq_aleph0`
    needs."
  apply Cardinal.mk_eq_aleph0

/---/
TheoremDoc instCountableRat as "instCountableRat" in "Cardinal"

/---/
TheoremDoc Cardinal.mk_eq_aleph0 as "Cardinal.mk_eq_aleph0" in "Cardinal"

NewTheorem Cardinal.mk_eq_aleph0 instCountableRat

NewDefinition Countable
