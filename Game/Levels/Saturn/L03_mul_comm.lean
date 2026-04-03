import Game.Metadata

World "Saturn"
Level 3

Title "[Saturn.L03] Title"

-- Introduction "Noch ein Funkspruch."
Introduction "Intro Saturn L03"

namespace MvPolynomial
Statement (P : MvPolynomial (Fin 2) ℚ) : (X 0) * P = P * (X 0) := by
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
  Hint "Explain `P`: `P` is a 'multivariate polynome' with variables indexed by `Fin 2` and
  coefficients in `ℚ`.
  Explain `Fin 2` as the set of elements $\\\{0,1\\}$ that lead to the variables `X 0` and `X 1`"
  ring

/-
Conclusion "
  Wieder ein 👍.
"
-/
Conclusion "Conclusion Saturn L03"
NewTactic ring

/-- [Saturn.L03] documentation 1-/
TheoremDoc mul_comm as "mul_comm" in "+ *"

NewTheorem mul_comm
NewDefinition Fin MvPolynomial
