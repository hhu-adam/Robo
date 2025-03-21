import Game.Metadata


World "Vieta"
Level 3

Title "" -- "Anonyme Funktionen"

Introduction
"
Wieder ein Pfeil.  Und noch eine Aufgabe.
"

Statement : ∃ f : ℤ → ℤ, ∀ x, f x < x := by
  Hint (hidden := true) "
    **Robo**: Wie immer gehst du ein `∃` mit `use …` an.  Oder du definierst dir erst einmal
    mit `let f : ℤ → ℤ := fun …` eine Abbildung, die du benutzen möchtest, so, wie du es eben gerade gesehen hast.
    Den Pfeil `↦` schreibst du übrigens als `\\maps` oder `\\mapsto`.
    Aber du kannst auch stattdessen `=>` benutzen."
  let f : ℤ → ℤ := fun x ↦ x -1
  Hint (strict := true) "**Robo**: Wenn du `{f}` richtig definiert hast, kannst du
  dieses mit `use` brauchen, und die resultierende Ungleichung sollte einfach sein"
  use f
  intro x
  Hint (hidden := true) "**Du**: Zu was sich das wohl vereinfacht?"
  simp [f]
  -- linarith

TheoremTab "Function"

Conclusion""

--NewTactic «let»
