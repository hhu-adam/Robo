import Game.Metadata

World "FunctionSurj"
Level 8

Title "Surjektive"

Introduction
"
Endlich kommt ihr in einen große, beleuchteten zentralen Raum.
Alle Wände sind voll mit Büchern und
in der Mitte sitzt an einem einsamen
Tisch ein Gelehrter, der tatsächlich das gesuchte Buch zeigen kann.

Bevor er dieses aushändigt, will er aber folgendes wissen:
"

open Function

Statement :
    let f := fun (n : ℤ) ↦ n + 1
    Surjective f := by
  Hint "**Robo**: Die Definition von `Surjective f` ist `∀ y, (∃ x, f x = y)`.

  **Du**: Dann kann ich das auch einfach wie Quantifier behandeln?

  **Robo**: Schieß drauf los!"
  intro y
  use y-1
  Hint (hidden := true) "
    **Du**: das is doch eigentlich ganz einfach… Kann man das denn
    noch weiter vereinfachen?

    **Robo**: Wenn du `{f}` auch einsetzt vermutlich schon."
  simp [f]

NewDefinition Function.Surjective
TheoremTab "Function"

Conclusion
"Der Gelehrte händigt euch schmunzelnd das Buch aus."
