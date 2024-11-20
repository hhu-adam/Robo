import Game.Metadata
import Game.Levels.Prado.L04_Two

namespace Nat

World "Prado"
Level 5

Title ""

Introduction
"
"

Statement not_prime_one : ¬ Nat.Prime 1 := by
  decide

TheoremTab "Nat"
