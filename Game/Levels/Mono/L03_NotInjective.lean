import Game.Levels.Mono.L02_InjectiveNeIff

open Nat

World "Mono"
Level 3

Title ""

-- Introduction ""
Introduction "Intro Mono L03"

open Function

Statement :
    let f : ℕ → ℕ := fun n ↦ if Even n then n^2 else n+1;
    ¬ Injective (f + f) := by
  /-
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
  -/
  Hint "Story"
  /-
  Hint (hidden := true) "
  **Robo**: Vielleicht öffnest du zuerst mal `Injective` mit `unfold`. Dann steht da `¬ ∀` …"
  -/
  Hint (hidden := true) "Try `Injective`, `unfold`"
  unfold Injective
  -- Hint (hidden := true) (strict := true) "**Robo**: Erinnerst du dich an `push_neg`?"
  Hint (hidden := true) (strict := true) "Try `push_neg`"
  push_neg
  /-
  Hint (hidden := true)"
    **Du** Jetzt muss ich einfach ein Gegenbeispiel nennen, oder?

    **Robo** Genau! Welche beiden Zahlen möchtest du denn verwenden?"
  -/
  Hint (hidden := true) "Try `use` with two numbers"
  use 2
  use 3
  -- Hint (hidden := true) "**Robo**:  Das ist hier alles so konkret, vielleicht reicht `decide`."
  Hint (hidden := true) "Try `decide`"
  decide

TheoremTab "Function"

-- Conclusion ""
Conclusion "Conclusion Mono L03"
