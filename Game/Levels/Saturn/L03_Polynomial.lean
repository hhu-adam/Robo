import Game.Metadata

World "Saturn"
Level 3

Title ""

Introduction "Intro Saturn L03:
`Polynomial ℚ` is a type of univariate polynomial over `ℚ`.
And `X` is the polynomial variable in the polynomial ring `ℚ[X]`. "

namespace Polynomial

Statement : (X : Polynomial ℚ) + X + X ^ 2 = X ^ 2 + 2 * X := by
  ring

Conclusion "Conclusion Saturn L03"

NewTactic ring

/---/
DefinitionDoc Polynomial as "Polynomial"

NewDefinition Polynomial Polynomial.X
