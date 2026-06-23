import Game.Metadata

World "Cafe"
Level 1

Title ""

/-
Introduction "
**Lina**:  Jetzt ich wieder.
"
-/
Introduction "Intro Cafe L01"

/- This Level used to be Luna 09. Here I think could be used to teach `grind` can
do thing `linarith` can do. -/
Statement (a c : ℝ) (h : a ≠ c): a < c ∨ c < a := by
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
  obtain h | h | h := lt_trichotomy a c
  · Hint "Try `grind`"
    grind
  · contradiction
  · Hint "Try `grind`"
    grind

/--
Wird typischerweise mit `obtain` verwendet, um in einem Beweis die drei Fälle `x < y`, `x = y` und `x > y` zu unterscheiden:

```
obtain h | h | h := lt_trichotomy x y
```
-/
TheoremDoc lt_trichotomy as "lt_trichotomy" in "≤"
NewTheorem lt_trichotomy

Conclusion "Cafe L01"
