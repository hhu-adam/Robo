import Game.Metadata

World "Cafe"
Level 4

Title ""

/-
Introduction "
**Lina**:  Jetzt ich wieder.
"
-/
Introduction "Intro Luna L09"

open Finset
Statement (a c : ℝ) (h : a ≠ c): ∃ b : ℝ, a < b ∧ b < c ∨ c < b ∧ b < a := by
  /-
  Hint "**Du**:
  Nun, es ist schon ziemlich klar, welches `b` man hier verwenden könnte.

  **Robo**: Wenn dir das so klar ist, dann fang doch schon einmal mit `use …` an.
  Und danach wirst du `lt_trichotomy` gut gebrauchen können.  Zum Beispiel so:
  ```
  obtain h | h | h := lt_trichotomy a c
  ```
  "
  -/
  Hint "It is clear which `b` can be used. Start with `use …` and continue with `lt_trichotomy` e.g.
  ```
  obtain h | h | h := lt_trichotomy a c
  ```
  "
  use (a + c) / 2
  grind

Conclusion "Cafe L04"
