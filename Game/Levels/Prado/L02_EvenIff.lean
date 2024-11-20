import Game.Metadata
import Game.Levels.Prado.L01_Dvd

namespace Nat

World "Prado"
Level 2

Title "Gerade"

Introduction
"
Hier nochmal eine kleine Übung für später.
"

Statement even_iff_two_dvd {a : ℕ} : Even a ↔ 2 ∣ a := by
  -- TODO: is there a shorter way?
  Hint (hidden := true) "fang doch mit `unfold Even` an."
  unfold Even
  constructor
  · intro h
    obtain ⟨w, hw⟩ := h
    use w
    rw [hw]
    ring
  · intro h
    obtain ⟨w, hw⟩ := h
    use w
    rw [hw]
    ring

TheoremTab "Nat"
