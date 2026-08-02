import Game.Metadata
import Mathlib.Analysis.Real.Cardinality

World "Uncountable"
Level 6

Introduction "Every set of rational numbers was countable. With the reals this breaks
down: Mathlib knows that the universal set of reals cannot be enumerated.

Here you turn that fact into the statement that the type `ℝ` itself is uncountable."

noncomputable section

open Function Cardinal

Statement : Uncountable ℝ := by
  Hint "[Hint rkmv] Being uncountable is nothing but *not* being countable, and
    `not_countable_iff` lets you switch between the two."
  rw [← not_countable_iff]
  Hint (hidden := true) "[Hint tzpc] `Set.countable_univ_iff` gets you back to the
    universal set, where `Cardinal.not_countable_real` applies."
  rw [← Set.countable_univ_iff]
  apply Cardinal.not_countable_real

/---/
TheoremDoc not_countable_iff as "not_countable_iff" in "Cardinal"

/---/
TheoremDoc Set.countable_univ_iff as "Set.countable_univ_iff" in "Set"

/---/
TheoremDoc Cardinal.not_countable_real as "Cardinal.not_countable_real" in "Cardinal"

NewTheorem not_countable_iff Set.countable_univ_iff Cardinal.not_countable_real
