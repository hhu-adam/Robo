import Game.Metadata

World "Luna"
Level 9

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
  obtain h | h | h := lt_trichotomy a c
  · left
    constructor
    linarith
    linarith
  · contradiction
  · right
    constructor
    linarith
    linarith

/-
Conclusion "
  **Lina**: Habt ihr gut gemacht!  Schade, dass ihr schon weiterfliegen müsst.
  Aber wenn ihr noch länger bleibt, bringt ihr unseren Tagesrhythmus völlig durcheinander.
  "
-/
Conclusion "Conclusion Luna L09"
