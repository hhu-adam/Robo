import Game.Metadata


open Nat

World "Luna"
Level 3

Title ""

/-
Introduction
"
**Lina**: Probierts doch mal hiermit!
"
-/
Introduction "Intro Luna L03"

/--
Wird typischerweise mit `obtain` verwendet, um in einem Beweis die drei Fälle `x < y`, `x = y` und `x > y` zu unterscheiden:

```
obtain h | h | h := lt_trichotomy x y
```
-/
TheoremDoc lt_trichotomy as "lt_trichotomy" in "≤"


Statement lt_trichotomy: ∀ a b : ℝ, a < b ∨ a = b ∨ b < a := by
  intro a b
  /-
  Hint (strict := true)"
    **Du**:  Fallunterscheidung ??

    **Robo**:  Ja, könntest du versuchen. Zum Beispiel erst `by_cases h_leq : {a} ≤ {b}` und dann `by_cases h_lt : {a} < {b}`.
  "
  -/
  Hint (strict := true) "Try `by_cases h_leq : {a} ≤ {b}`, `by_cases h_lt : {a} < {b}`"
  by_cases h_leq : a ≤ b
  · by_cases h_lt : a < b
    · left
      assumption -- or linarith
    · right
      left
      /-
      Hint "
        **Du**:  Und jetzt??

        **Lina** (*triumphal*): `linarith`!
        "
      -/
      Hint "Now try `linarith`!"
      linarith  -- WANT LINARITH in this exercise!
  · right
    right
    linarith -- WANT LINARITH in this exercise!

NewTactic linarith

TheoremTab "≤"

/-
Conclusion "
  **Lina**:  Ihr hättet übrigens auch einfach `apply lt_trichotomy` sagen können.
"
-/
Conclusion "Conclusion Luna L03: Alternatively `apply lt_trichotomy` could have been used."
