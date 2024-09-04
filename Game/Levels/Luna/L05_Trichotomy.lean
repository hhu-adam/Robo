import Game.Metadata

World "Luna"
Level 5

Title "Trichotomie"

Introduction
"
"

Statement {A : Prop} (x y : ℤ) (h₁ : x ≤ y → A) (h₂ : y < x → A) : A := by
  Hint (strict := true) "
    **Robo**: Ein sehr nützliches Resultat ist `lt_trichotomy {x} {y}`:

    ${x} < {y}$ oder ${x} = {y}$ oder ${x} > {y}$

    Typischerweise kann man dieses wie folgt verwenden:

    ```
    obtain h | h | h := lt_trichotomy x y
    ```
  "
  obtain h | h | h := lt_trichotomy x y
  · Hint "**Robo**: Beachte, dass du jetzt 3 Goals hast, eines pro Fall!"
    apply h₁
    linarith
  · apply h₁
    linarith
  · apply h₂
    assumption

Conclusion ""

NewTheorem lt_trichotomy