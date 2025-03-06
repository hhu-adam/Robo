import Mathlib

/-
   Idea is to sum over Icc 0 n instead of Fin (n+1)
   This makes proofs a bit longer but gives more flexibility,
   and ties in better with the product over all primes considered elsewhere.
   Generally, the difference is that 

        rw [sum_univ_castSucc]
   
   needs to be replaced by something along the lines of
   
        rw [← insert_Icc_eq_Icc_add_one_right]  
        · rw [sum_insert]
          · …
          · simp
        · linarith

   ISSUES:  see Babylon L03
-/

open Nat Finset BigOperators

/- Babylon L01 -/
example (A : Finset ℕ) : (∑ i ∈ A, (0 + 0)) = 0 := by
  simp

/- Babylon L02 -/
example (n : ℕ) : ∑ i ∈ Icc 1 n, 2 = 2 * n := by
  simp
  ring

/- Babylon L03 -/
-- old version:
example (n : ℕ) : ∑ i : Fin n, ( (i : ℕ)  + 1) = n + (∑ i : Fin n, (i : ℕ) ) := by
  rw [sum_add_distrib]
  simp
  ring

-- new suggestion fails:
example (n : ℕ) : ∑ i ∈ Icc 1 n, i + 1 = n + (∑ i ∈ Icc 1 n, i) := by
  rw [sum_add_distrib] -- did not find instance of pattern in target expression
  sorry

/- Babylon L04 -/  
theorem arithmetic_sum (n : ℕ) : 2 * (∑ i ∈ Icc 0 n, i) = n * (n + 1) := by
    induction' n with d hd
    · simp
    · rw [← insert_Icc_eq_Icc_add_one_right] 
      -- or rw [← Icc_insert_succ_right], but as above is more general, see theorem zero_sum
      · rw [sum_insert]
        · rw [mul_add, hd]
          ring
        · simp
      · simp  --or linarith

/- Babylon L05 -/
example (n : ℕ) : (∑ i ∈ Icc 0 n, (2 * i + 1)) = (n + 1)^ 2 := by
  induction' n with d hd
  · simp
  · rw [← insert_Icc_eq_Icc_add_one_right] 
    · rw [sum_insert]
      · rw [hd]
        ring
      · simp
    · linarith

/- Babylon L06 -/      
example (n m : ℕ) : ∑ i ∈ Icc 0 n, ∑ j ∈ Icc 0 m, (2 ^ i * (1 + j)) =
    ∑ j ∈ Icc 0 m, ∑ i ∈ Icc 0 n, (2 ^ i * (1 + j)) := by
  rw [sum_comm]

/- Babylon L07 -/  
example (m : ℕ) : (∑ i ∈ Icc 0 m, i ^ 3) = (∑ i ∈  Icc 0 m, i) ^ 2 := by
  induction' m with n n_ih
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

/- Babylon:  potential new level that was not possible before -/
example (n : ℕ) : ∑ i ∈ Icc (-n : ℤ) n, i = 0 := by
    induction' n with d hd
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

