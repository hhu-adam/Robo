import Game.Metadata

World "Cafe"
Level 3

Title ""

/-
Introduction "
**Lina**:  Jetzt ich wieder.
"
-/
Introduction "Intro Cafe L03"

/- This Level used to be Luna 09. Here I think could be used to teach `grind` can
do thing `linarith` can do. -/
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
  use (a + c) / 2
  Hint "[Hint grindDirect] No need to split into cases with `lt_trichotomy` this time — `grind`
  handles the case analysis and the inequalities on its own. Just try `grind` right away."
  grind

Conclusion "Cafe L03"
