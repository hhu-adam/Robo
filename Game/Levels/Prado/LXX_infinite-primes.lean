import Mathlib

open Set BigOperators
namespace Nat

theorem Euclid : ¬ Set.Finite { p : ℕ | Prime p} := by
  by_contra hf
  -- notation to make equations human-readable:
  let all_primes := { p : ℕ | Prime p}
  let all_primes' := hf.toFinset
  let prod : ℕ := ∏ p ∈ all_primes', p
  let new_prime : ℕ := prod + 1
  -- main observation:
  have h_main (p : ℕ) (hp : Prime p) : ∃ q : ℕ, q > 0 ∧ new_prime = p*q + 1 := by
    let parprod := ∏ p' ∈ all_primes'.erase p, (p' : ℕ)
    use parprod
    constructor
    · apply Finset.prod_pos
      intro p'
      simp[all_primes']
      intro h hp
      rw [prime_def] at hp
      linarith
    · have h : prod = p * parprod := by
        symm
        apply Finset.mul_prod_erase all_primes' id
        · simp[all_primes']
          assumption
      rw [← h]
  -- As for any natural number > 1, there must be some prime that divides new_prime:
  have h_exists_prime_factor : ∃ p : ℕ, Nat.Prime p ∧ p ∣ new_prime := by
    have : 1 < new_prime := by
      have : Nat.Prime 2 := by
        decide
      specialize h_main 2 this
      obtain ⟨q, hq⟩ := h_main
      linarith
    apply exists_prime_and_dvd
    linarith
  -- On the other hand, by construction, no prime divides new_prime:
  have h_no_prime_divides : ∀ p : ℕ, Nat.Prime p →  ¬ p ∣ new_prime := by
    intro p hp
    specialize h_main p hp
    obtain ⟨ q, hq, h ⟩ := h_main
    rw[h]
    apply Nat.not_dvd_of_between_consec_multiples (n := p) (k:=q) (m := p*q+1)
    · linarith
    · ring
      have : 1 < p := by
        simp[prime_def] at hp
        linarith
      linarith
  -- So now, we have a contradiction:
  obtain ⟨p, hp, h_dvd⟩ := h_exists_prime_factor
  specialize h_no_prime_divides p hp
  contradiction

/- main things that need to be introduced and explained:

- Finset
- Finset.erase
- Finset.prod (∏)
- Finset.prod_pos
- Finset.mul_prod_erase
- Set.Finite
- Set.Finite.toFinset
- Nat.exists_prime_and_dvd
- Nat.not_dvd_of_between_consec_multiples
-/
