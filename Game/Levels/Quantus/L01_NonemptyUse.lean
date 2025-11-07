import Game.Metadata

World "Quantus"
Level 1

Title "" -- "Natürliche Zahlen"

-- Introduction "Auf der Vorderseite steht folgendes."
Introduction "`INTRO` Intro Quantus L01"

Statement : Nonempty ℕ := by
  -- Hint "**Du**: Ich soll zeigen, dass es eine natürlich Zahl gibt?
  --
  -- **Robo**: Genau.  Dazu gibts du mit `use _` einfach irgendeine natürlich Zahl an."
  Hint "Show that there is a natural number by `use _`"
  use 0

-- Conclusion "Ihr dreht das Blatt um."
Conclusion "`CONC` Conclusion Quantus L01"

NewTactic use
NewDefinition Nonempty
