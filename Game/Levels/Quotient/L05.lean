import Game.Metadata

World "Quotient"
Level 5

Statement : ∀ n, ∃ (s : Finset ℝ), Finset.card s = n := by
  intro n
  apply Infinite.exists_subset_card_eq ℝ n
