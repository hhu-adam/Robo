import Mathlib

open BigOperators Finset Nat

/- Finset.range n  is the set of natural numbers {0,…,n-1}.
! Finset.range  should not be confused with  Function.range  !
-/

variable (n : ℕ)

#check Icc 0 n
#check Icc (-n : ℤ) n
#check range n

example (n : ℕ) : Finset ℕ := by
  --exact range n
  exact Icc 0 n

example (d : ℕ) : d ∉ range d := by
  --exact not_mem_range_self
  simp


-- Finset.range allows a fairly natural formulation of the arithmetic sum exercise without any casts:

theorem arithmetic_sum (n : ℕ) :
    2 * (∑ i ∈ range (n+1), i) = n * (n + 1) := by
    induction' n with d hd
    · simp
    · rw [range_add_one]
      rw [sum_insert]
      · rw [mul_add, hd]
        ring
      · simp


-- Finset.range also allows the following alternative proof with erase instead of insert:

lemma Finset.range_erase (d : ℕ) : (range (d + 1)).erase d = range d := by
  rw [erase_eq_iff_eq_insert]
  exact range_add_one
  exact self_mem_range_succ d
  exact not_mem_range_self

theorem arithmetic_sum' (n : ℕ) :
    2 * (∑ i ∈ range (n+1), i) = n * (n + 1) := by
    induction' n with d hd
    · simp
    · --have h : d + 1 ∈ range (d + 1 + 1) := by
      --  simp
      rw [←add_sum_erase]
      rw [range_erase]
      rw [mul_add, hd]
      ring
      simp

-- Icc also allows an even more natural formulation – no need for "n+1" in the formulation of the sum
-- (but proof is one simp longer than for range):

theorem arithmetic_sum'' (n : ℕ) :
    2 * (∑ i ∈ Icc 0 n, i) = n * (n + 1) := by
    induction' n with d hd
    · simp
    · rw [← insert_Icc_eq_Icc_add_one_right]
      -- or rw [← Icc_insert_succ_right], but as above is more general, see theorem zero_sum
      · rw [sum_insert]
        · rw [mul_add, hd]
          ring
        · simp
      · simp  --or linarith


-- Icc gives more flexibility, e.g. we can also formulate the following sum:

theorem zero_sum (n : ℕ) :
    ∑ i ∈ Icc (-n : ℤ) n, i = 0 := by
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
