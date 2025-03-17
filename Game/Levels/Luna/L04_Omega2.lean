import Game.Metadata


open Nat

World "Luna"
Level 4

Title ""

Introduction
"
  **Lina**:  Hier habe ich noch etwas.
"

Statement (l m n x : ℕ) (h₁ : l ≤ m) (h₂ : m ≤ n) : l ≤ x ∧ x ≤ n → ¬ (m ≤ x ∧ x ≤ n) → x ≤ m := by
  Hint "Ritha scheint euch mit ihren Augen irgendein Zeichen geben zu wollen."
  omega

TheoremTab "ℕ"

Conclusion "
  **Lina**:  Ja, okay, mein Fehler.
"
