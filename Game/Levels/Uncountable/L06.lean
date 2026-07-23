import Game.Metadata
import Mathlib.Data.Rat.Encodable

World "Uncountable"
Level 6

noncomputable section

open Function Cardinal

/- There is a one theorem proof `Set.countable_univ`. But I would like to introduce these
theorem, which will be used in the boss level.  -/

Statement : (Set.univ : Set ℚ).Countable := by
  Hint "[Hint univQ] Since `ℚ` is countable, every set of rationals is countable.
    The theorem `Set.countable_univ` says exactly this for the universal set."
  rw [← Cardinal.le_aleph0_iff_set_countable]
  rw [Cardinal.mk_univ]
  rw [Cardinal.mk_eq_aleph0]

/---/
TheoremDoc Set.countable_univ as "Set.countable_univ" in "Set"

/---/
TheoremDoc Cardinal.le_aleph0_iff_set_countable as "Cardinal.le_aleph0_iff_set_countable" in "Cardinal"

/---/
TheoremDoc Cardinal.mk_univ as "Cardinal.mk_univ" in "Cardinal"

NewTheorem Set.countable_univ Cardinal.le_aleph0_iff_set_countable Cardinal.mk_univ
