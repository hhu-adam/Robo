import Game.Metadata

World "Saturn"
Level 3

-- Introduction "Noch ein Funkspruch."
Introduction "Intro Saturn L03"

namespace Polynomial
Statement (P : ℚ[X]) : X * P = P * X := by
  /-
  Hint "
    **Du**:  Nanu, was ist denn `P` hier für ein Tier?

    **Robo**: `P` ist ein “multivariates Polynom”, wobei die Variablen mit `Fin 2`
    durchnummeriert sind und die Koeffizienten in `ℚ` liegen.

    **Du**:  Und was ist `Fin 2`?

    **Robo**:  Die Standardmenge mit zwei Elementen – $\\\{0,1\\}$.  Die Variablen heißen also `X 0` und `X 1`.

    **Du**:  Spielt hier aber eigentlich alles keine Rolle, oder?  Der Polynomring ist doch kommutativ!

    **Robo**: So ist es.
  "
  -/
  Hint "Explain `P`: `P` is a polynomial over rational number `ℚ`."
  ring

/-
Conclusion "
  Wieder ein 👍.
"
-/
Conclusion "Conclusion Saturn L03"
NewTactic ring

/---/
TheoremDoc mul_comm as "mul_comm" in "+ *"

NewTheorem mul_comm
NewDefinition Polynomial Polynomial.X
