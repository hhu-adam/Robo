import Game.Metadata

World "SetTheory"
Level 11

Title "" -- "Abschluss"

Introduction
"
Viel Spass!
"

open Set

Statement : {2, 7} ⊆ {n : ℕ | n = 2 ∨ (n ≤ 10 ∧ Odd n)} := by
  intro x
  intro h
  simp at *
  obtain h | h := h
  · tauto
  · simp [h]
    decide

TheoremTab "Set"

Conclusion ""
