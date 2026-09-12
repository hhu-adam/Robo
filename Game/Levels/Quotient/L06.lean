import Game.Metadata
import Game.Levels.Quotient.L05

World "Quotient"
Level 6

Introduction "Intro Quotient L06"

noncomputable section

open FiniteSets

Statement :
    Quotient isoSetoid ≃ ℕ := by
  Hint "[Hint q6clas] All finite sets modulo the isomorphic relation is equivalent to natural number."
  Hint (hidden := true) "[Hint q6ofbij] The map is `cardMap`, built two levels ago, and
    `Equiv.ofBijective` upgrades a bijective map to an equivalence — leaving you to show that
    it is injective and surjective."
  apply Equiv.ofBijective cardMap
  constructor
  · intro x y h
    induction x using Quotient.ind
    induction y using Quotient.ind
    apply Quotient.sound
    apply Finite.card_eq.mp h
  · intro n
    use ⟦of (Fin n)⟧
    simp [cardMap, of]
