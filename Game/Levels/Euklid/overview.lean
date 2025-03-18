import Game.Metadata
/-
main things that need to be introduced and explained:

**Drafted for Piazza**:
- `Finset`
- `Finset.erase`
- `Finset.insert`
- `Finset.insert_erase`

**Drafted for Prado**
- `Nat.exists_prime_and_dvd`
- `Nat.not_dvd_of_between_consec_multiples`

**Here: Finite/infinite sets:**
- `Set.Finite`
- `Set.Finite.toFinset`

**Here: Products**
- `Finset.prod` (`∏`)
- `Finset.prod_pos`
- `Finset.prod_insert`      -- analogous to Finset.add_insert, used in draft of Babylon
-/

open Finset BigOperators

namespace Nat

/- Euklid 01:
   - `Finset.prod` (`∏`) (product notation)
   - `prod_pos`          (product of positive integers is positive)
-/
-- preliminary exercise with just two factors: `mul_pos` (not strictly necessary)
/-
example (a b : ℕ) (ha : Prime a) (hb : Prime b) : 0 < a*b  := by
  apply mul_pos
  sorry
-/
example (A : Finset ℕ) (h : ∀ a ∈ A, Prime a) : 0 < (∏ a ∈ A, a) := by
  apply prod_pos
  intro a ha
  specialize h a ha
  rw [prime_def] at h
  linarith


/- Euklid 02:
   - `prod_insert`
  This is the direction ← of `Prime.dvd_finset_prod_iff`,
  except that that lemmas uses `_root_.Prime`.
-/
example (p : ℕ) (hp : Prime p) (A : Finset ℕ): (∃ a ∈ A, p ∣ a) → p ∣ ∏ a ∈ A, a := by
  intro h
  obtain ⟨a, ha, hpa⟩ := h
  rw [← insert_erase ha]
  rw [prod_insert]
  · rw [Prime.dvd_mul]
    · left
      assumption
    · assumption
  · simp

/- Euklid 03:
   - `Set.Finite`
   - `Set.toFinite`
  (- and `prod_insert`, again)
  IFF set of primes is finite, then there exists a number such that p ∣ a for all primes p!
-/
example (hf : Set.Finite { p : ℕ | Prime p}) : ∃ (a : ℕ), ∀ (p : ℕ), Prime p → p ∣ a := by
  let all_primes := hf.toFinset
  use ∏ p ∈ all_primes, p
  intro p hp
  -- previous lemma would be useful now, but want to practise!
  have hp' : p ∈ all_primes := by
    simp [all_primes]
    assumption
  rw [← insert_erase hp']
  rw [prod_insert]
  · use ∏ x ∈ all_primes.erase p, x
  · simp

/- Euklid 04:  BOSS -/
example : ¬ Set.Finite { p : ℕ | Prime p} := by
  by_contra hf
  -- notation to make equations human-readable:
  let all_primes := hf.toFinset
  let prod : ℕ := ∏ p ∈ all_primes, p
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
    let q := ∏ p' ∈ (all_primes.erase p), (p' : ℕ)
    -- new_prime = p * q + 1 …
    have h : prod = p * q := by
      /- slightly longer version that uses prod_insert: -/
      simp[prod]
      have : p ∈ all_primes := by
        simp[all_primes]
        assumption
      rw[← Finset.insert_erase this]
      apply Finset.prod_insert
      simp
      /- shorter, older version that used mul_prod_erase: -/
      /-
      symm
      apply Finset.mul_prod_erase all_primes id
      simp[all_primes]
      assumption
      -/
    simp[new_prime]
    rw [h]
    -- … so it cannot be divisible by p:
    apply not_dvd_of_between_consec_multiples (n := p) (k:=q) (m := p*q+1)
    · linarith
    · simp [prime_def] at hp
      linarith
  -- Now we have a contradiction:
  obtain ⟨p, hp, h_dvd⟩ := h_exists_prime_factor
  specialize h_no_prime_divides p hp
  contradiction


/- ---------------------------------------------------- -/

/- An application of `Prime.dvd_finset_prod_iff` -/
/- … was supposed to be a fairly easy exercise, just for getting used to notation … -/
/-
example (A : Set ℕ) (hA : Set.Finite A): Even (∏ a ∈ hA.toFinset, a) ↔ ∃ a ∈ hA.toFinset, (Even a) := by
  constructor
  · intro h
    rw [even_iff_two_dvd] at h
    rw [Prime.dvd_finset_prod_iff] at h
    · obtain ⟨a, ha, ha'⟩ := h
      use a
      rw [even_iff_two_dvd]
      constructor
      · assumption
      · assumption
    sorry
  · sorry
-/
