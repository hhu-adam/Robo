import Game.Metadata

World "Quotient"
Level 1

Introduction "Intro Quotient L01"

/---/
TheoremDoc Finite.card_eq as "Finite.card_eq" in "Quotient"

Statement Finite.card_eq {α β : Type*} [Finite α] [Finite β] :
    Nat.card α = Nat.card β ↔ Nonempty (α ≃ β) := by
  Hint "[Hint q1cnt] Two finite types have the same number of
    elements exactly when their elements can be paired off one by one. `Nonempty (α ≃ β)` is how
    Lean says that such a bijection *exists*, without naming a particular one."
  apply Finite.card_eq

NewTheorem Finite.card_eq
