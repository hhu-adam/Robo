import Game.Metadata
import Game.Levels.Quotient.L02

World "Quotient"
Level 3

open Pointwise

Introduction "Intro Quotient L03"

/- TODO: explain the Finset.neg here. Notation `-s`. -/
Statement {s : Finset ℝ} :
    (⟦s⟧ : Quotient isoSetoid) = ⟦-s⟧ := by
  apply Quotient.sound
  apply Fintype.card_eq.mp
  simp
  -- rw [Fintype.card_coe, Fintype.card_coe, Finset.card_neg]
