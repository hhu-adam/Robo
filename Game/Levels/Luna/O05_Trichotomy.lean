import Game.Metadata

World "Luna"
Level 5

Title "" -- "Trichotomie"

/-
Introduction
"
"
-/
Introduction "Intro Luna O05"

Statement {A : Prop} (x y : ℤ) (h₁ : x ≤ y → A) (h₂ : y < x → A) : A := by
  /-
  Hint (strict := true) "
    **Robo**: Ein sehr nützliches Resultat ist `lt_trichotomy {x} {y}`:

    ${x} < {y}$ oder ${x} = {y}$ oder ${x} > {y}$

    Typischerweise kann man dieses wie folgt verwenden:

    ```
    obtain h | h | h := lt_trichotomy x y
    ```
  "
  -/
  Hint "Try `obtain h | h | h := lt_trichotomy x y`"
  obtain h | h | h := lt_trichotomy x y
  -- · Hint "**Robo**: Beachte, dass du jetzt 3 Goals hast, eines pro Fall!"
    Hint "Story"
    apply h₁
    linarith
  · apply h₁
    linarith
  · apply h₂
    assumption

-- Conclusion ""
Conclusion "Conclusion Luna O05"

/--
Wird typischerweise mit `obtain` verwendet, um in einem Beweis die drei Fälle `x < y`, `x = y` und `x > y` zu unterscheiden:

```
obtain h | h | h := lt_trichotomy x y
```
-/
TheoremDoc lt_trichotomy as "lt_trichotomy" in "…"
NewTheorem lt_trichotomy
