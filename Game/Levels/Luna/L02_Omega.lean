import Game.Metadata


open Nat

World "Luna"
Level 2

Title ""

Introduction
"
**Lina**: Außerdem muss man zum Beispiel wissen, dass `0 < n` oder `n < 0` für ganze Zahlen nichts anderes
bedeutet als `n ≠ 0`.
"

Statement (n : ℤ) : 0 < n ∨ n < 0 ↔ n ≠ 0 := by
  Hint "**Ritha** *(flüsternd)*: Probiert mal `omega`!"
  omega

NewTactic omega

TheoremTab "ℕ"

Conclusion "Lina rollt die Augen.

**Lina**: Ritha ist ein großer Fan von `omega`.  Dabei ist `omega` ziemlich impotent.
Sobald man die ganzen Zahlen verlässt, kann `omega` gar nichts mehr.

**Ritha**:  Selber impotent!

Ritha macht eine unanständige Grimasse.
"
