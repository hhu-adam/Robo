import Game.Metadata

World "Saturn"
Level 5

Introduction "Intro Saturn L05"

/- a well-known polyonmial sums-of-squares formula --/

namespace MvPolynomial

Statement (A B :  MvPolynomial (Fin 4) ℝ) (hA : A = X 0 * X 3 - X 1 * X 2)
    (hB : B = X 0 * X 2 + X 1 * X 3) :
    (X 0 ^ 2 + X 1 ^ 2) * (X 2 ^ 2 + X 3 ^ 2) = A ^ 2 + B ^ 2 := by
  Hint "[Hint sat5] Explain `A B`: `A B` are 'multivariate polynome' with variables
  indexed by `Fin 4` and coefficients in `ℝ`.
  Explain `Fin 4` as the set of elements $\\\{0,1, 2, 3\\}$ that lead to the variables
  `X 0`, `X 1`, `X 2` and `X 3`."
  rw [hA, hB]
  ring

NewDefinition Fin MvPolynomial MvPolynomial.X

TheoremTab "+ *"

/-
Conclusion "
  “Bestanden” heißt es kurz und knapp vom anonymen Funker.

  **Robo**: Ich glaube, der Antrieb hat sich jetzt genügend regeniert.
  Nichts wie weg!
"
-/
Conclusion "Conclusion Saturn L05"
