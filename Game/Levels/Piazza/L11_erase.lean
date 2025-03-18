import Game.Metadata

World "Piazza"
Level 11

Title ""

Introduction "
**Mem**:  Hey, Fin, wachst machst Du denn da?

Fin ist der kleinste in der Runde und hat bislang nichts gesagt.
Und jetzt hat er anscheinend gerade vom Stand nebenan eine Pistazie geklaut.

**Fin**:  Ist doch nur eine kleine Übung.

**Mem**: Was für eine Übung?

Fin erklärt sich folgendermaßen.
"

open Set

Statement (A : Finset ℕ) (a : ℕ) : Finset.erase A a = A \ {a} := by
  Hint "
    **Du**:  Was bedeutet denn hier jetzt `Finset`?

    **Robo**:  Das bedeutet, dass `A` zu den *endlichen* Teilmengen von ℕ gehört.
    Macht aber für die Frage eigentlich keinen Unterschied.
    Links steht `A` ohne `a`, rechts steht auch `A` ohne `a`.
    "
  ext
  simp
  tauto

TheoremTab "Set"

Conclusion ""

NewDefinition Finset.erase
