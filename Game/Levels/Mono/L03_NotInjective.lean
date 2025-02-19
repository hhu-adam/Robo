import Game.Metadata

open Nat

World "Mono"
Level 3

Title ""

Introduction ""

open Function

Statement :
    let f : ℕ → ℕ := fun n ↦ if Even n then n^2 else n+1;
    ¬ Injective (f + f) := by
  Hint "**Du**:  Also, die gegebene Abbildung hat die folgende Form:
  $$
  f(n) = \\begin\{cases}
    n^2 & \\text\{falls } n \\text\{ gerade} \\\\
    n+1 & \\text\{andernfalls.}
  \\end\{cases}
  $$
  Und was ist `f + f`?

  **Robo**: Das ist die Abbildung `ℕ → ℕ`, die an jeder Stelle den doppelten Wert von `f` annimmt.
  "
  Hint (hidden := true) "
  **Robo**: Vielleicht öffnest du zuerst mal `Injective` mit `unfold`. Dann steht da `¬ ∀` …"
  unfold Injective
  Hint (hidden := true) (strict := true) "**Robo**: Erinnerst du dich an `push_neg`?"
  push_neg
  Hint (hidden := true)"
    **Du** Jetzt muss ich einfach ein Gegenbeispiel nennen, oder?

    **Robo** Genau! Welche beiden Zahlen möchtest du denn verwenden?"
  use 2
  use 3
  Hint (hidden := true) "**Robo**:  Das ist hier alles so konkret, vielleicht reicht `decide`."
  decide

TheoremTab "Function"

Conclusion ""
