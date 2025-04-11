import Game.Metadata

World "Saturn"
Level 3

Title ""

Introduction "Noch ein Funkspruch."

namespace MvPolynomial

Statement (a b c : MvPolynomial (Fin 4) ℕ ) : a * b * c = a * (b * c) := by
  Hint "**Robo** Hier könntest du `mul_assoc` verwenden.  Oder *wieder* `ring` …"
  ring

Conclusion "
  Wieder ein 👍.

  **Du**: Aber warte mal, diesmal waren die Koeffizienten doch in `ℕ`!
  Das ist doch gar kein Ring, und auch Polynome mit Koeffizienten in `ℕ` bilden keinen Ring.

  **Robo**: Mag sein.  Aber `ring` funktioniert sogar für sogenannte Halbringe.

  **Du**: So so …
"

NewTactic ring

/---/
TheoremDoc mul_assoc as "mul_assoc" in "+ *"

NewTheorem mul_assoc
