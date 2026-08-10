import Game.Metadata
import Game.Levels.Cantor.L11_SequenceUncountable

World "Uncountable"
Level 7

Introduction "Intro Uncountable L07"

open Function

/---/
TheoremDoc nat_seq_uncountable as "nat_seq_uncountable" in "Cardinal"

Statement nat_seq_uncountable : Uncountable (ℕ → ℕ) := by
  Hint "[Hint u7bgf] Remember that Cantor already
  showed you that no sequence of sequences can list all sequences of natural numbers.
  Time to translate that magic trick into the language of cardinalities: here you deduce
  that the type `ℕ → ℕ` is uncountable."
  Hint "[Hint qvtd] Start as in the previous level and get rid of `Uncountable`."
  rw [← not_countable_iff]
  Hint (hidden := true) "[Hint sfnv] A nonempty type is countable exactly when some
    sequence enumerates it — `countable_iff_exists_surjective` then leaves you with
    precisely the statement Cantor made you prove."
  rw [countable_iff_exists_surjective]
  apply not_surjective_nat_seq

/---/
TheoremDoc countable_iff_exists_surjective as "countable_iff_exists_surjective" in "Cardinal"

NewTheorem countable_iff_exists_surjective
