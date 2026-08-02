import Game.Metadata
import Mathlib.Data.Rat.Encodable

World "Uncountable"
Level 5

Introduction "Intro Uncountable L05"

noncomputable section

open Function Cardinal

/- There is a one theorem proof `Set.countable_univ`. But I would like to introduce these
theorem, which will be used in the boss level.  -/

Statement : (Set.univ : Set ℚ).Countable := by
  Hint "[Hint univQ] Since `ℚ` is countable, every set of rationals is countable.
    The theorem `Set.countable_univ` says exactly this for the universal set."
  rw [← Cardinal.le_aleph0_iff_set_countable]
  Hint (hidden := true) "[Hint u5sfs] Try `simp`."
  simp

/---/
TheoremDoc Cardinal.le_aleph0_iff_set_countable as "Cardinal.le_aleph0_iff_set_countable" in "Cardinal"

NewTheorem Cardinal.le_aleph0_iff_set_countable
