import Game.Metadata
import Game.Levels.Prado.L07_ExistsUnique

namespace Nat

World "Prado"
Level 8

Title "Gerade Primzahlen"

Introduction
"
"

Statement : ∃! (p : ℕ), Nat.Prime p ∧ Even p := by
  use 2
  simp
  constructor
  · decide
  · intro y h₁ h₂
    Hint (hidden := true) "Schau mal durch die Aussagen, die du bisher bewiesen hattest.
    Du brauchst zwei davon."
    rw [even_iff_two_dvd] at h₂
    rw [prime_dvd_prime_iff_eq] at h₂
    · symm
      assumption
    · decide
    · assumption

TheoremTab "Nat"
