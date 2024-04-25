import Game.Metadata

World "Cantor"
Level 4

Title "Odd fixed points"

Introduction
"
Bei einer ungeraden Funktionen sind Fixpunkte symmetrisch um Null herum.
"

open Function Set Setoid

Statement {f : ℝ → ℝ} (h_odd : ∀ x, f (-x) = - f x) :
    IsFixedPt f x ↔ IsFixedPt f (- x) := by
  constructor
  · intro h
    unfold IsFixedPt
    rw [h_odd x]
    rw [h]
  · intro h
    unfold IsFixedPt at h
    rw [h_odd x] at h
    rw [neg_inj] at h
    assumption

NewTheorem neg_inj
TheoremTab "Function"
