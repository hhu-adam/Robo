import Game.Metadata
import Game.Levels.Prime.L07_InfinitudePrimes

World "Prime"
Level 8

Title "Unendlich viele Primzahlen"

Introduction "
"

Conclusion "
"

-- Damit die Notation `n !` funktionieren.
open Nat Set

Statement Nat.exists_infinite_primes' :
    let allPrimes := { p : ℕ | Prime p }
    ¬ Set.Finite allPrimes := by
  by_contra h
  -- TODO: how to do this nicely
  have ⟨q, _hq₁, hq₂⟩ := Set.Finite.exists_maximal_wrt (id : ℕ → ℕ) allPrimes h ?_
  · simp? at hq₂
    have l03 := Nat.exists_infinite_primes (q+1)
    rcases l03 with ⟨P, hP₁, hP₂⟩
    have hP₃ : q ≤ P := by
      apply le_of_succ_le
      assumption
    apply hq₂ at hP₃
    . rw [hP₃] at hP₁
      -- this is a proof by contradiction
      apply not_succ_le_self P
      assumption
    · rw [mem_setOf]
      assumption
  · use 2
    trivial

#check pred_inj