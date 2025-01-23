import Game.Metadata

World "Quantus"
Level 1

Title "Natürliche Zahlen"

Introduction "Du schaust dir die erste Seite an."

Statement : Nonempty ℕ := by
  Hint "**Du**: Ich soll zeigen, dass es eine natürlich Zahl gibt?

  **Robo**: Genau.  Dazu gibts du mit `use _` einfach irgendeine natürlich Zahl an."
  use 0

Conclusion ""

NewTactic use
