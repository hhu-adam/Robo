import Game.Metadata
import Game.Levels.Prime.L05_MinFacPrime

World "Prime"
Level 6

Title "Unendlich viele Primzahlen"

Introduction "
**Person**: Warte mal, ist die wirklich grösser als $n$?

**Du**: Na klar!

"

Conclusion "**Person**: Die ist schon mal grösser als die grösste Zahl, die ich je angeschaut
habe!
"

-- Damit die Notation `n !` funktionieren.
open Nat

Statement le_minFac_factorial_succ (n : ℕ) : n ≤ minFac (n ! + 1) := by
  by_contra h
  rw [not_le] at h
  apply le_of_lt at h
  have h₁ : minFac (n ! + 1) ∣ n ! := dvd_factorial (minFac_pos _) h
  apply Nat.Prime.not_dvd_one (minFac_factorial_succ_prime n)
  exact (Nat.dvd_add_iff_right h₁).2 (minFac_dvd _)
