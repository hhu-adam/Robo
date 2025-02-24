import Game.Metadata

World "Euklid"
Level 1

open Set BigOperators
namespace Nat

Statement : ¬ Set.Finite { p : ℕ | Prime p} := by
  by_contra hf
  -- notation to make equations human-readable:
  let all_primes := hf.toFinset
  let prod : ℕ := Finset.prod all_primes id
  -- TODO: change to
  -- let prod : ℕ := BigOperators.bigprod p ∈ all_primes, p
  let new_prime : ℕ := prod + 1
  -- As for any natural number > 1, there must be some prime that divides new_prime:
  have h_exists_prime_factor : ∃ p : ℕ, Prime p ∧ p ∣ new_prime := by
    have : 1 < new_prime := by
      have : 0 < prod  := by
        apply Finset.prod_pos
        intro p
        simp[all_primes]
        intro h
        rw [prime_def] at h
        linarith
      simp[new_prime]
      assumption
    apply exists_prime_and_dvd
    linarith
  -- On the other hand, by construction, no prime divides new_prime:
  have h_no_prime_divides : ∀ p : ℕ, Prime p →  ¬ p ∣ new_prime := by
    intro p hp
    let q := Finset.prod (all_primes.erase p) id
    -- TODO: change to
    -- let q := ∏ p' ∈ all_primes.erase p, (p' : ℕ)
    --
    -- new_prime = p * q + 1 …
    have h : prod = p * q := by
      symm
      apply Finset.mul_prod_erase all_primes id
      simp[all_primes]
      assumption
    simp[new_prime]
    rw [h]
    -- … so it cannot be divisible by p:
    apply not_dvd_of_between_consec_multiples (n := p) (k:=q) (m := p*q+1)
    · linarith
    · simp[prime_def] at hp
      linarith
  -- Now we have a contradiction:
  obtain ⟨p, hp, h_dvd⟩ := h_exists_prime_factor
  specialize h_no_prime_divides p hp
  contradiction




/-
main things that need to be introduced and explained:

- Finset
- Finset.erase
- Finset.prod (∏)
- Finset.prod_pos
- Finset.mul_prod_erase
→ **Babylon** ?
Currently all sums in babylon are over Fin n, because the main point is induction!
Can we have induction over Finsets instead?
In any case, does make sense to include products in Babylon as well.

- Set.Finite
- Set.Finite.toFinset
→ **Piazza**

- Nat.exists_prime_and_dvd
- Nat.not_dvd_of_between_consec_multiples
→ **Prado** -- should easily fit in
-/
