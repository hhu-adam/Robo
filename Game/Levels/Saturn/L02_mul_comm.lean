import Game.Metadata

World "Saturn"
Level 2

Title ""

Introduction "Noch ein Funkspruch."

namespace MvPolynomial
Statement (P : MvPolynomial (Fin 2) ℚ) : (X 0) * P = P * (X 0) := by
  Hint "
    **Du**:  Nanu, was ist denn `P` hier für ein Tier?

    **Robo**: `P` ist ein “multivariantes Polynom”, wobei die Variablen mit `Fin 2`
    durchnummeriert sind und die Koeffizienten in `ℚ` liegen.

    **Du**:  Und was ist `Fin 2`?

    **Robo**:  Die Standardmenge mit zwei Elementen – $\\\{0,1\\}$.  Die Variablen heißen also `X 0` und `X 1`.

    **Du**:  Spielt hier aber eigentlich alles keine Rolle, oder?  Der Polynomring ist doch kommutativ!

    **Robo**: So ist es.
  "
  ring

Conclusion "
  Wieder ein 👍.
"
NewTactic ring

/---/
TheoremDoc mul_comm as "mul_comm" in "+ *"

NewTheorem mul_comm
NewDefinition Fin
