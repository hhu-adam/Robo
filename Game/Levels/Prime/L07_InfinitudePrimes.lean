import Game.Metadata
import Game.Levels.Prime.L06_MinFacGE

World "Prime"
Level 7

Title "Unendlich viele Primzahlen"

Introduction "
"

Conclusion "
"

-- Damit die Notation `n !` funktionieren.
open Nat

/-- Zeige, dass es unendlich viele Primzahlen gibt -/
Statement Nat.exists_infinite_primes (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p := by
  -- based on project by Maren
  Hint "**Du**: `minFac (n ! + 1)` ist der kleinste Primfaktor von $n! + 1$"

  let q := minFac (n ! + 1)
  use q
  constructor
  · apply le_minFac_factorial_succ n
  · apply minFac_factorial_succ_prime n
