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
Statement (a c : ℝ) (h : a ≠ c) : a < c ∨ c < a := by
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
  Hint "[Hint lt] Try to use the theorem `lt_trichotomy` to discuss relations between `a` and `c`
  ```
  obtain h | h | h := lt_trichotomy a c
  ```
  "
  obtain h | h | h := lt_trichotomy a c
  · Hint "[Hint tg1] Try `grind`"
    grind
  · contradiction
  · Hint (hidden := true) "[Hint tg2] **Scribble**: Well, I guess you just try `grind` again."
    grind

/--
Wird typischerweise mit `obtain` verwendet, um in einem Beweis die drei Fälle `x < y`, `x = y` und `x > y` zu unterscheiden:

```
obtain h | h | h := lt_trichotomy x y
```
-/
TheoremDoc lt_trichotomy as "lt_trichotomy" in "≤"
NewTheorem lt_trichotomy

/-- To add. -/
TacticDoc grind
NewTactic grind


Conclusion "Cafe L01"
