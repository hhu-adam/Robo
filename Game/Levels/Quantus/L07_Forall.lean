import Game.Metadata

World "Quantus"
Level 7

Title "" -- "Für alle"

-- Introduction "Nach längerem Durcheinander findet folgende Aufgabe aus der Menge zu Euch."
Introduction "`INTRO` Intro Quantus L07"

Statement : ∀ (x : ℕ), (Even x) → Odd (1 + x) := by
  /-
  Hint "
    **Du**: Das `∀` heisst sicher \"für alle\".

    **Robo**: Und man schreibt `\\forall`. Ein `∀ x, …` im Beweisziel kannst du wie eine
    Implikation mit `intro x` angehen."
  -/
  Hint "Explain `∀` i.e. `\\forall` and approch to prove `∀ x, …`  by `intro x`"
  intro x h
  unfold Even at h
  unfold Odd
  choose y hy using h
  use y
  rw [hy]
  ring

NewDefinition Forall

/-
Conclusion
"
Wieder anerkennendes Nicken.

Wieder Getuschel.
"
-/
Conclusion "`CONC` Conclusion Quantus L07"
