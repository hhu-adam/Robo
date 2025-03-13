import Game.Metadata

World "Quantus"
Level 10

Title "" -- "Für alle"

Introduction "Nach längerem Durcheinander findet folgende Aufgabe aus der Menge zu Euch."

Statement : ∀ (x : ℕ), (Even x) → Odd (1 + x) := by
  Hint "
    **Du**: Das `∀` heisst sicher \"für alle\".

    **Robo**: Und man schreibt `\\forall`. Ein `∀ x, …` im Beweisziel kannst du wie eine
    Implikation mit `intro x` angehen."
  intro x h
  unfold Even at h
  unfold Odd
  choose y hy using h
  use y
  rw [hy]
  ring

NewDefinition Forall

Conclusion
"
Wieder anerkennendes Nicken.

Wieder Getuschel.
"
