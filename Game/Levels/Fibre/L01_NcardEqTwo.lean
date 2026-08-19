import Game.Levels.Bolzano.L06_CrossRight

World "Fibre"
Level 1

Introduction "Intro Fibre L01"

open Set FullGrind

/-- A set has exactly two elements precisely when it is of the form `{x, y}` with `x < y`. -/
TheoremDoc ncard_eq_two_lt as "ncard_eq_two_lt" in "Fibre"

Statement ncard_eq_two_lt {s : Set ℝ} : s.ncard = 2 ↔ ∃ x y, x < y ∧ s = {x, y} := by
  rw [Set.ncard_eq_two]
  constructor
  · intro h
    obtain ⟨x, y, hxy, hs⟩ := h
    have hcases : x < y ∨ x > y := lt_or_gt_of_ne hxy
    obtain h | h := hcases
    · use x, y
    · use y, x
      grind
  grind

NewTheorem Set.ncard_eq_two lt_or_gt_of_ne

TheoremTab "Fibre"
