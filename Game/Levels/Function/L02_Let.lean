import Game.Metadata


World "Function"
Level 2

Title "Anonyme Funktionen"

-- TODO: story
Introduction
"
Ihr macht euch auf in Richtung Bibliothek entlang kleiner Pfade zwischen verschiedensten Behausungen.

**Du**: Sag mal, wie definiert ich denn selber eine Funktion?

**Robo**: Das kannst du mit `let f := fun (x : ℤ) ↦ x + 1` machen. Hier, probier mal:
"

Statement : ∃ f : ℤ → ℤ, ∀ x, f x < x := by
  Hint (hidden := true) "
    **Robo**: Wie immer gehst du ein `∃` mit `use …` an."
  let f := fun (x : ℤ) ↦ x - 1
  Hint (strict := true) "**Robo**: Wenn du `{f}` richtig definiert hast, kannst du
  dieses mit `use` brauchen, und die resultierende Ungleichung sollte einfach sein"
  use f
  intro x
  Hint (hidden := true) "**Du**: Zu was sich das wohl vereinfacht?"
  simp [f]
  -- linarith

TheoremTab "Function"

Conclusion
"
"

NewTactic «let»
