import Game.Metadata

World "Quantus"
Level 1

Title "" -- "Natürliche Zahlen"

Introduction "Auf der Vorderseite steht folgendes."

Statement : Nonempty ℕ := by
  Hint "**Du**: Ich soll zeigen, dass es eine natürlich Zahl gibt?

  **Robo**: Genau.  Dazu gibts du mit `use _` einfach irgendeine natürlich Zahl an."
  use 0

Conclusion "Ihr dreht das Blatt um."

NewTactic use
NewDefinition Nonempty
