import Game.Metadata
import Game.Levels.Prado.L02_dvd_iff_exists_eq_mul_left


World "Prado"
Level 3

Title ""

/-
Introduction
"Während ihr Guino durch das Museum folgt, gibt dir Robo weitere Aufgaben.
"
-/
Introduction "Intro Prado L03"

/---/
TheoremDoc Nat.even_iff_two_dvd as "even_iff_two_dvd" in "ℕ"

namespace Nat

Statement even_iff_two_dvd {a : ℕ} : Even a ↔ 2 ∣ a := by
  -- Hint (hidden := true) "
  --   **Robo**:  Fang doch noch einmal mit `rw [dvd_iff_exists_eq_mul_left]` an!
  -- "
  Hint "Begin with `rw [dvd_iff_exists_eq_mul_left]`"
  Branch
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
  rw [dvd_iff_exists_eq_mul_left]
  unfold Even
  ring

TheoremTab "ℕ"
