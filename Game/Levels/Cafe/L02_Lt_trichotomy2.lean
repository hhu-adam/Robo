import Game.Metadata

World "Cafe"
Level 2

Title ""

/-
Introduction "
**Lina**:  Jetzt ich wieder.
"
-/
Introduction "Intro Cafe L02"

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
  Hint "It is clear which `b` can be used. Start with `use …` and continue with `lt_trichotomy` e.g.
  ```
  obtain h | h | h := lt_trichotomy a c
  ```
  "
  use (a + c) / 2
  obtain h | h | h := lt_trichotomy a c
  · Hint "[Hint ulgrd] Since `a < c`, I'd say the left side of the `∨` is the one that holds. Pick it with `left`."
    left
    Hint "[Hint ltgrind] The goal is now a system of inequalities. `grind` is good at this kind of
    arithmetic reasoning, so just try `grind`."
    grind
  · contradiction
  · right
    Hint (hidden := true) "I guess you can try `grind` again."
    grind

/-- To add. -/
TacticDoc grind

NewTactic grind

Conclusion "Cafe L02"
