import Game.Metadata


open Nat

World "Luna"
Level 4

Title ""

/-
Introduction
"
  **Lina**:  Hier habe ich noch etwas.
"
-/
Introduction "`INTRO` Intro Luna L04"

Statement (l m n x : ℕ) (h₁ : l ≤ m) (h₂ : m ≤ n) : l ≤ x ∧ x ≤ n → ¬ (m ≤ x ∧ x ≤ n) → x ≤ m := by
  -- Hint "Ritha scheint euch mit ihren Augen irgendein Zeichen geben zu wollen."
  Hint "`COMMENT` Try omega"
  omega

TheoremTab "ℕ"

/-
Conclusion "
  **Lina**:  Ja, okay, mein Fehler.
"
-/
Conclusion "`CONC` Conclusion Luna L04"
