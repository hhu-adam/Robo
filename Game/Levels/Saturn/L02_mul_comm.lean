import Game.Metadata

World "Saturn"
Level 2

Title ""

Introduction "Noch ein Funkspruch."


Statement (a b : ℕ) : a * b = b * a := by
  ring

Conclusion "
  Wieder ein 👍.

  **Du**: Aber halt, diesmal sind die Variablen doch in `ℕ`!
  Das ist doch gar kein Ring!

  **Robo**: Ist es nicht.  Aber `ring` funktioniert sogar für sogenannte Halbringe.
  Und die Aussage hier heißt übrigens `mul_eq_mul`.

  **Du**: So so …
"
NewTactic ring

/---/
TheoremDoc mul_comm as "mul_comm" in "Ring"

NewTheorem mul_comm
DisabledTheorem mul_comm
