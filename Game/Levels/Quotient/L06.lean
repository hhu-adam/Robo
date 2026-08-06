import Game.Metadata
import Game.Levels.Quotient.L03

World "Quotient"
Level 6

noncomputable section

Statement isoQuotientEquivNat (α : Type*) [Infinite α] :
    Quotient (isoSetoid) ≃ ℕ := by
  apply Equiv.ofBijective (Quotient.lift Finset.card (fun _ _ h ↦ card_eq_iff_equiv.mpr h))
  constructor
  · intro x y h
    induction x using Quotient.ind
    induction y using Quotient.ind
    apply Quotient.sound
    apply Fintype.card_eq.mp
    simp_log
    exact h
  · intro n
    obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq ℝ n
    use ⟦s⟧
    assumption
