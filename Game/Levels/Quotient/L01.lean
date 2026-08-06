import Game.Metadata

World "Quotient"
Level 1

Introduction "Intro Quotient L01"

Statement card_eq_iff_equiv {s t : Finset ℝ} :
    s.card = t.card ↔ Nonempty (s ≃ t) := by
  rw [← Fintype.card_eq]
  simp
