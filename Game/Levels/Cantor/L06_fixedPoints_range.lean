import Game.Metadata

World "Cantor"
Level 6

Title "Idemptonent fixed points"

open Function Set

Statement range_fixedPoints (f : A → A) (h : f ∘ f = f) : range f = fixedPoints f := by
  apply Subset.antisymm
  · intro x hx
    rcases hx
    rw [← h_1]
    unfold fixedPoints
    unfold IsFixedPt
    rw [mem_setOf]
    apply congr_fun at h -- :D
    simp only [comp_apply] at h
    rw [h]
  · intro x hx
    rw [mem_range] -- is simp
    use x
    trivial
