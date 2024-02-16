import Game.Metadata

World "TmpInfinitudePrimes"
Level 1

Title "Unendlich viele Primzahlen"

-- TODO: Proof by Maren

Introduction ""

-- Damit die Notation `n !` funktionieren.
open Nat

/-- Zeige, dass es unendlich viele Primzahlen gibt -/
Statement Nat.exists_infinite_primes (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p := by
  -- based on project by Maren
  let q := minFac (n ! + 1)
  use q
  have q_prime : Nat.Prime q
  · apply minFac_prime
    Branch
      simp [Nat.ne_of_gt, factorial_pos]
    intro h
    apply factorial_ne_zero n
    apply succ_inj.mp
    assumption
  constructor
  · by_contra h
    rw [not_le] at h
    apply le_of_lt at h
    have h₁ : q ∣ n ! := dvd_factorial (minFac_pos _) h
    apply q_prime.not_dvd_one
    exact (Nat.dvd_add_iff_right h₁).2 (minFac_dvd _)
  · assumption

NewTheorem Nat.minFac_prime Nat.minFac_pos Nat.minFac_dvd
  Nat.dvd_add_iff_right Nat.dvd_factorial Nat.Prime.not_dvd_one
  Nat.factorial_ne_zero Nat.succ_inj Nat.factorial_pos Nat.ne_of_gt
NewDefinition Nat.minFac Nat.Prime Nat.factorial
