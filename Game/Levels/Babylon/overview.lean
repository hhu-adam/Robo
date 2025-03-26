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
example (I : Finset ℕ) : ∑ i ∈ I, 2 = 2 * card I := by
  simp
  ring


/- Babylon L03:  sum_congr -- needed for second sum_subset exercise below -/
example (I : Finset ℕ) : ∑ i ∈ I, (((i : ℤ) + 1)^2 - i^2 - 2*i)  = (card I : ℤ)  := by
  have h (i : ℕ) : (i+1)^2 - i^2 - 2*i = (1 : ℤ) :=  by
    ring
  trans  ∑ i ∈ I, (1 : ℤ)
  apply sum_congr
  · rfl
  · intro i hi
    apply h
  · simp


/- Babylon 04: introduce  sum_subset , needed for ROBOTSWANA -/
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


/- Babylon 05: more interesting, second exercise on sum_subset
   Problems:
   - { i ∈ I | Even i} was rendered in a strange way, but it seems Jon has fixed this
   - last step is a bit unexpected, see Note at the end, but is prepared above
-/

set_option pp.all false  -- not sure what this means

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
      rw [← odd_iff_not_even] at h
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

/- Babylon L06 -/
section Babylon06
open Robo.NN.Finset
theorem arithmetic_sum (n : ℕ) : (∑ i ∈ Icc 0 n , i : ℚ) = 1/2  * n * (n + 1) := by
    induction n with d hd
    · simp
    · rw [← insert_Icc_eq_Icc_add_one_right]
      -- or rw [← Icc_insert_succ_right], but as above is more general, see theorem zero_sum
      · rw [sum_insert]
        · rw [hd]
          simp
          ring
        · simp
      · linarith

theorem Robo.NN.arithmetic_sum (n : ℕ) : 2 * (∑ i ∈ Icc 0 n , i) = n * (n + 1) := by
    induction n with d hd
    · simp
    · rw [← insert_Icc_eq_Icc_add_one_right]
      -- or rw [← Icc_insert_succ_right], but as above is more general, see theorem zero_sum
      · rw [sum_insert]
        · rw [mul_add, hd]
          ring
        · simp
      · linarith

end Babylon06

/- Babylon 07: good exercise for repeating what has been leaned in L06 -/
section Babylon07
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
end Babylon07

/- Babylon L08 -/
section Babylon08
open Robo.NN.Finset
example (n : ℕ) : (∑ i ∈ Icc 0 n, (2 * i + 1)) = (n + 1)^ 2 := by
  induction n with d hd
  · simp
  · rw [← insert_Icc_eq_Icc_add_one_right]
    · rw [sum_insert]
      · rw [hd]
        ring
      · simp
    · linarith
end Babylon08

/- Babylon L09:  version in ℚ
   Statement in ℚ is easier to prove,
   Statement in ℕ seems more natural,
   but deduction of ℕ-statement from ℚ-statement is unfortunately cumbersome, see below.
   I decided to use the ℚ-statement, without any conversion.
-/
section Babylon09Q
open Robo.NN.Finset
example (m : ℕ) : (∑ i ∈ Icc 0 m, (i : ℚ) ^3) = (∑ i ∈  Icc 0 m, i : ℚ)^2 := by
  induction m with n n_ih
  · simp
  · rw [← insert_Icc_eq_Icc_add_one_right]
    · rw [sum_insert]
      · simp
        rw [n_ih]
        rw [arithmetic_sum]
        simp
        ring
      · simp
    · linarith
end Babylon09Q

/-
   Statement in ℕ feels more natural but is more difficult to prove,
   even with ℕ-version of arithmetic sum:
-/
section Babylon09N
open Robo.NN.Finset
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
        rw [Robo.NN.arithmetic_sum]
        ring
      · simp
    · linarith
end Babylon09N

/- Conversion from ℕ to ℚ works as follows: -/
example (m : ℕ) (hQ: (∑ i ∈ Icc 0 m, (i : ℚ) ^3) = (∑ i ∈  Icc 0 m, i : ℚ)^2) :
  (∑ i ∈ Icc 0 m, i ^ 3) = (∑ i ∈  Icc 0 m, i) ^ 2 := by
  have hQ' : (↑(∑ i ∈ Icc 0 m, (i^3 : ℕ)) : ℚ) = (↑((∑ i ∈  Icc 0 m, i)^2 : ℕ) : ℚ) := by
    --simp_all only [cast_sum, cast_pow]
    simp
    assumption
  rw [Nat.cast_inj] at hQ'
  assumption

/- simpler example of this: -/
example (a b : ℕ) (hQ : (a : ℚ) = (b : ℚ)) : a = b := by
  rw [Nat.cast_inj] at hQ -- or: rw [← @Nat.cast_inj ℚ]
  assumption



/- Further ideas for induction exercises -/

example (n : ℤ) : 3 ∣ n^3 + 2*n := by
  sorry

example (n : ℕ) : (n - 1) * (n + 1) = (n ^ 2 - 1) := by
  sorry

example (x : ℕ) (n : ℕ) : 1 + n * x ≤ (x + 1) ^ n := by
  sorry

example (n : ℕ) : (∑ i : Fin (n + 1), 2 * i - 1) = n ^ 2 := by
  sorry

example  (n : ℕ) : (n + 5)^2 < 2 ^ (n + 5) := by
  sorry

example (n : ℕ) (h : 5 ≤ n) : n^2 < 2 ^ n := by
  sorry

/- obsolete levels ------------------------------------/

/- Babylon O03: sum_add_distrib -- NOT NEEDED -/
/-
example (n : ℕ) : ∑ i ∈ Icc 1 n, (i + 1) = n + (∑ i ∈ Icc 1 n, i) := by
  rw [sum_add_distrib]
  simp
  ring
-/

/- Babylon O06: `summ_comm` -- NOT NEEDED -/
/-
example (n m : ℕ) : ∑ i ∈ Icc 0 n, ∑ j ∈ Icc 0 m, (2 ^ i * (1 + j)) =
    ∑ j ∈ Icc 0 m, ∑ i ∈ Icc 0 n, (2 ^ i * (1 + j)) := by
  rw [sum_comm]
-/
