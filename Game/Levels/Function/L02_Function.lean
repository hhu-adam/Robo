import Game.Metadata


World "Function"
Level 2

Title "Anonyme Funktionen"

-- TODO: story
Introduction
"
"

Statement : ∃ f : ℤ → ℤ, ∀ x, f x < x := by
  Hint (hidden := true) "
    **Robo**: Wie immer gehst du ein `∃` mit `use …` an."
  use (fun x ↦ x - 1)
  Hint (hidden := true) "**Du**: Zu was sich das wohl vereinfacht?"
  Branch
    intro x
    Hint (hidden := true) "**Du**: Zu was sich das wohl vereinfacht?"
    simp
  simp

TheoremTab "Function"

Conclusion
"
Das Mädchen wird kurz ruhig, dann beginnt es zu lächeln und zeigt strahlend
in eine Richtung. Ihr folgt ihrem Finger und euch fällt in weiter ferne eine pompöse Struktur
auf einem flachen Hügel auf.
"
