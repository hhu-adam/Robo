import Game.Metadata
import Game.Levels.Quotient.L01

World "Quotient"
Level 2

Introduction "Intro Quotient L02"

Statement isoSetoid: Setoid (Finset ℝ) := by
  refine' { r s t := Nonempty (s ≃ t), ..}
  constructor
  · intro x
    apply Fintype.card_eq.mp rfl
  · intro x y hxy
    apply Fintype.card_eq.mp
    symm
    apply Fintype.card_eq.mpr
    assumption
  · intro x y z hxy hyz
    obtain h1 := Fintype.card_eq.mpr hxy
    obtain h2 := Fintype.card_eq.mpr hyz
    apply Fintype.card_eq.mp
    grind
