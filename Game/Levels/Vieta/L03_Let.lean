import Game.Metadata


World "Vieta"
Level 3

Title "" -- "Anonyme Funktionen"

/-
Introduction
"
Wieder ein Pfeil.  Und noch eine Aufgabe.
"
-/
Introduction "`INTRO` Intro Vieta L03"

Statement : ∃ f : ℤ → ℤ, ∀ x, f x < x := by
  /-
  Hint (hidden := true) "
    **Robo**: Wie immer gehst du ein `∃` mit `use …` an.  Oder du definierst dir erst einmal
    mit `let f : ℤ → ℤ := fun …` eine Abbildung, die du benutzen möchtest, so, wie du es eben gerade gesehen hast.
    Den Pfeil `↦` schreibst du übrigens als `\\maps` oder `\\mapsto`.
    Aber du kannst auch stattdessen `=>` benutzen."
  -/
  Hint (hidden := true) "Tackle  `∃` either with `use …` or define mapping `let f : ℤ → ℤ := fun …` as before. Remind that `↦` is either `\\maps` or `\\mapsto` ro can be replyced by `=>`"
  let f : ℤ → ℤ := fun x ↦ x -1
  -- Hint (strict := true) "**Robo**: Wenn du `{f}` richtig definiert hast, kannst du
  -- dieses mit `use` brauchen, und die resultierende Ungleichung sollte einfach sein"
  Hint (strict := true) "If `{f}` correctly defind try `use`"
  use f
  intro x
  -- Hint (hidden := true) "**Du**: Zu was sich das wohl vereinfacht?"
  Hint (hidden := true) "Try `simp`"
  simp [f]
  -- linarith

TheoremTab "Function"

-- Conclusion""
Conclusion "Conclusion Vieta L03"

--NewTactic «let»
