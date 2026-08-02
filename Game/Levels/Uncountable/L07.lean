import Game.Metadata
import Game.Levels.Cantor.L11_SequenceUncountable

World "Uncountable"
Level 7

Introduction "So far everything you met was countable. But in his tent, Cantor already
showed you that no sequence of sequences can list all sequences of natural numbers.

Time to translate that magic trick into the language of cardinalities: here you deduce
that the type `ℕ → ℕ` is uncountable."

open Function

Statement : Uncountable (ℕ → ℕ) := by
  Hint "[Hint qvtd] Being uncountable is nothing but *not* being countable, and
    `not_countable_iff` lets you switch between the two."
  rw [← not_countable_iff]
  Hint (hidden := true) "[Hint sfnv] A nonempty type is countable exactly when some
    sequence enumerates it — `countable_iff_exists_surjective` then leaves you with
    precisely the statement Cantor made you prove."
  rw [countable_iff_exists_surjective]
  apply not_surjective_nat_seq

/---/
TheoremDoc not_countable_iff as "not_countable_iff" in "Cardinal"

/---/
TheoremDoc countable_iff_exists_surjective as "countable_iff_exists_surjective" in "Cardinal"

NewTheorem not_countable_iff countable_iff_exists_surjective
