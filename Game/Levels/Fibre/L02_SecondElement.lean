import Game.Levels.Fibre.L01_NcardEqTwo

World "Fibre"
Level 2

Introduction "Intro Fibre L02"

open Set FullGrind

/-- A two-element set contains a second element besides any given one. -/
TheoremDoc exists_second_mem as "exists_second_mem" in "Fibre"

Statement exists_second_mem {A : Type} {S : Set A} {a : A} (h : S.ncard = 2) (ha : a ∈ S) :
    ∃ b ∈ S, b ≠ a := by
  rw [Set.ncard_eq_two] at h
  obtain ⟨x, y, hxy, hS⟩ := h
  simp [hS] at ha ⊢
  grind

TheoremTab "Fibre"
