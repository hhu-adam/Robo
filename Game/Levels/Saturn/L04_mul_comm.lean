import Game.Metadata

World "Saturn"
Level 4

Introduction "Intro Saturn L04"

namespace Polynomial
Statement (P : ℚ[X]) : X * P = P * X := by
  Hint "Explain: `P` is polynomial over `ℚ` with indeterminate `X`"
  ring

Conclusion "Conclusion Saturn L04"
NewTactic ring

/---/
TheoremDoc mul_comm as "mul_comm" in "+ *"

NewTheorem mul_comm
NewDefinition Polynomial Polynomial.X
