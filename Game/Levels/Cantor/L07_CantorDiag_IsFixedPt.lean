import Game.Metadata
import Game.Levels.Cantor.L06_idempotent

World "Cantor"
Level 8

Title "Diagonalargument"

Introduction
"
**Cantor**: Genug gerätselt, jetzt aber zum Diagonalargument. Wenn wir eine surjektive
Funktion `f : A → (A → Y)` haben, dann hat jede Funktion `s : Y → Y` einen Fixpunkt.

**Du**: Und welcher Punkt ist das?

**Cantor**: Gute Frage! Hier, ich geb euch eine Aufgabe um das herauszufinden.
"

open Function Set

Statement cantor_diagonal_isFixedPt {f : A → A → Y} {s : Y → Y}
    (c : A → Y) (c_def : ∀ a, c a = s (f a a)) {b : A} (hb : f b = c) :
    IsFixedPt s (f b b) := by
  Hint "**Cantor**: Diese Aufgabe soll euch vermitteln, wie ihr den Fixpunkt kriegt!"
  unfold IsFixedPt
  rw [← c_def]
  rw [hb]

Conclusion "**Du**: Also ist der Fixpunkt dieses diagonale Element `f b b`, für ein `b`
  das irgendwie aus der Surjektivität kommt…

  **Cantor**: Und damit auf zum Hauptsatz!"

TheoremTab "Function"
