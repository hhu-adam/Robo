import Game.Levels.Bolzano.L06_CrossRight

World "Fibre"
Level 1

Introduction "Intro Fibre L01"

open Set FullGrind

Statement ncard_eq_two_lt {s : Set ℝ} : s.ncard = 2 ↔ ∃ x y, x < y ∧ s = {x, y} := by
  rw [Set.ncard_eq_two]
  constructor
  · intro ⟨x, y, hxy, hs⟩
    obtain h | h := lt_or_gt_of_ne hxy
    · use x, y
    · use y, x
      grind
  grind

NewTheorem Set.ncard_eq_two lt_or_gt_of_ne
