import Game.Metadata
/-
   Idea is to sum over Icc 0 n instead of Fin (n+1)
   This makes proofs a bit longer but gives more flexibility,
   and ties in better with the product over all primes considered elsewhere.
   Generally, the difference is that

        rw [sum_univ_castSucc]

   needs to be replaced by something along the lines of

        rw [← Icc_insert_succ_right]
        · rw [sum_insert]
          · …
          · simp
        · linarith
-/

open Nat Finset
-- TODO: do NOT open `BigOperators`, or the old mathlib delaborator takes precedence

/- Babylon L01:  preparation for second sum_subset exercise below -/
example (I : Finset ℕ) : (∑ i ∈ I, 1) = card I := by
  simp

/- Babylon L02:  preparation for second sum_subset exercise below -/
example (I : Finset ℕ) (n : ℕ) (h : n = 2): ∑ i ∈ I, 2 = 2 * card I := by
  simp
  ring


/- Babylon NEW:  sum_congr -- needed for second sum_subset exercise below -/
example (I : Finset ℕ) : ∑ i ∈ I, (((i : ℤ) + 1)^2 - i^2 - 2*i)  = (card I : ℤ)  := by
  have h (i : ℕ) : (i+1)^2 - i^2 - 2*i = (1 : ℤ) :=  by
    ring
  trans  ∑ i ∈ I, (1 : ℤ)
  apply sum_congr
  · rfl
  · intro i hi
    apply h
  · simp

/- Babylon L03: sum_add_distrib -- NOT NEEDED -/
example (n : ℕ) : ∑ i ∈ Icc 1 n, (i + 1) = n + (∑ i ∈ Icc 1 n, i) := by
  rw [sum_add_distrib]
  simp
  ring

/- Babylon NEW: introduce  sum_subset , needed for ROBOTSWANA -/
example (n : ℕ) (hn : 3 ≤ n) : ∑ i ∈ Icc 0 n, (i^3 - 3 * i^2 + 2*i : ℤ ) = ∑ i ∈ Icc 3 n, (i^3 - 3*i^2 + 2*i : ℤ) := by
  symm
  apply sum_subset
  · rw [Icc_subset_Icc_iff] -- needs to be introduced in PIAZZA
    constructor
    linarith
    linarith
    assumption
  · -- showing that x = 0 or 1 or 2:  see Luna L??
    intro x h0 h3
    have h : x = 0 ∨ x = 1 ∨ x = 2 := by
      simp at h0 h3
      omega
    obtain hx | hx | hx  := h
    all_goals rw [hx]
    all_goals ring


/- Babylon NEW: more interesting, second exercise on sum_subset
   Problems:
   - { i ∈ I | Even i} is rendered in a strange way
   - last step is a bit unexpected, see Note at the end, but is prepared above
-/

set_option pp.all false

variable (I : Finset ℕ)

example (I : Finset ℕ) : ∑ i ∈ I, ((-1 : ℤ)^i + 1 : ℤ ) = 2*card { i ∈ I | Even i} := by
  trans ∑ i ∈ { i ∈ I | Even i}, ((-1 : ℤ)^i + 1 : ℤ)
  · symm
    apply sum_subset
    · simp
    · simp
      intro i h hI
      apply hI at h
      rw [Odd.neg_pow]
      ring
      rw [← not_even_iff_odd] at h
      assumption
  · trans ∑ i ∈ { i ∈ I | Even i}, (2 : ℤ)
    have : ∀ i ∈ { i ∈ I | Even i}, (-1 : ℤ)^i + 1 = 2 := by
      intro i hi
      simp at hi
      obtain ⟨hI, heven⟩ := hi
      rw [Even.neg_pow]
      ring
      assumption
    apply sum_congr   -- introduced in new exercise above
    · simp
    · assumption
    simp -- see Note below for this last step
    ring

/- Note:
     For some reason, I CANNOT solve the following:    -/
example (R : Type) [Ring R] (r : R) (A : Finset R) : ∑ a ∈ A, r*a = r * ∑ a ∈ A, a := by
  sorry

/-   However, it seems we don't need it: -/
example (I : Finset ℕ) : ∑ i ∈ I, 2 = 2*card I := by
  simp
  ring


/- Babylon L04 -/
section Babylon04a
open Finset
theorem arithmetic_sum (n : ℕ) : 2 * (∑ i ∈ Icc 0 n , i) = n * (n + 1) := by
    induction n with d hd
    · simp
    · rw [← insert_Icc_eq_Icc_add_one_right]
      -- or rw [← Icc_insert_succ_right], but as above is more general, see theorem zero_sum
      · rw [sum_insert]
        · rw [mul_add, hd]
          ring
        · simp
      · linarith
end Babylon04a

/- Babylon NEW: good exercise for repeating what has been leaned in L04 -/
section Babylon04b
open Robo.ZZ.Finset
example (n : ℕ) : ∑ i ∈ Icc (-n : ℤ) n, i = 0 := by
    induction n with d hd
    · simp
    · simp
      rw [← insert_Icc_eq_Icc_add_one_right]
      · rw [sum_insert]
        · have : (-1 : ℤ)  + -↑d  = -↑d - 1 := by
            ring
          rw [this]
          rw [← insert_Icc_eq_Icc_sub_one_left]
          · rw [sum_insert]
            · rw [hd]
              ring
            · simp
          · linarith
        · simp
      · linarith
end Babylon04b

/- Babylon L05 -/
section Babylon05
open Finset
example (n : ℕ) : (∑ i ∈ Icc 0 n, (2 * i + 1)) = (n + 1)^ 2 := by
  induction n with d hd
  · simp
  · rw [← insert_Icc_eq_Icc_add_one_right]
    · rw [sum_insert]
      · rw [hd]
        ring
      · simp
    · linarith
end Babylon05

/- Babylon L06 -/
example (n m : ℕ) : ∑ i ∈ Icc 0 n, ∑ j ∈ Icc 0 m, (2 ^ i * (1 + j)) =
    ∑ j ∈ Icc 0 m, ∑ i ∈ Icc 0 n, (2 ^ i * (1 + j)) := by
  rw [sum_comm]

/- Babylon L07 -/
section Babylon07
open Finset
example (m : ℕ) : (∑ i ∈ Icc 0 m, i ^ 3) = (∑ i ∈  Icc 0 m, i) ^ 2 := by
  induction m with n n_ih
  · simp
  · rw [← insert_Icc_eq_Icc_add_one_right]
    · rw [sum_insert]
      · simp
        rw [n_ih]
        -- arrive here faster now, no need for syntax of the form
        -- `sum_univ_castSucc (n := {n} + 1)` syntax
        rw [add_pow_two]      -- still needs to be introduced earlier
        rw [mul_comm 2 (n+1)] -- 1. these two steps were not necessary
        rw [mul_assoc]        -- 2.      in previous approach
        rw [arithmetic_sum]
        ring
      · simp
    · linarith
end Babylon07
