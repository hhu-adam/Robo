import Game.Metadata
import Game.Levels.Prado.L02_Dvd

namespace Nat

World "Prado"
Level 3

Title "Gerade"

Introduction
"Während ihr Guino durch das Museum folgt, gibt dir Robo weitere Aufgaben.
"

/---/
TheoremDoc Nat.even_iff_two_dvd as "even_iff_two_dvd" in "ℕ"

Statement even_iff_two_dvd {a : ℕ} : Even a ↔ 2 ∣ a := by
  -- TODO: is there a shorter way?
  Hint (hidden := true) "**Robo**: Fang doch mit `unfold Even` an."
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

TheoremTab "ℕ"
