import Game.Metadata
import Game.Levels.Prado.L02_Dvd

namespace Nat

World "Prado"
Level 3

Title ""

Introduction
"Guino wirkt inzwischen ein wenig irritiert, dass ihr gar keinen Augen für sein tolles Museum habt.
Er fühlt sich ignoriert. Um eure Aufmerksamkeit zu bekommen, gibt er euch folgende Aufgabe.
"

Statement : ∃ p : ℕ, Prime p ∧ p ∣ 99 := by
  use 11
  decide

TheoremTab "ℕ"
