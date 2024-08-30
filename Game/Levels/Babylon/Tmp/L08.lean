import Game.Metadata

open Fin BigOperators Set

example (n : ℕ) : ∑ i : Fin n, ↑ i = ∑ i : Fin n, (n - i) := by
  sorry

example : ∑ i : Fin 10, i = 45 := by
  rfl

example : ∑ i : Fin 10, (10 - i) = 45 := by
  rfl

example : ∑ i : Fin 10, (3 - (i : ℕ)) = 6 := by
  apply sum_trunc (a:= 4) (b:= 6)
  intro j
  fin_cases j <;> simp only [natAdd] <;> rfl

-- def finUnion {α : Type*} (B : Finset (Set α)) : Set α :=
--   B.fold (∪) ∅ id  -- cool!

#check Set.iUnion
#check Set.union

-- def fold (b : β) (f : α → β) (s : Finset α) : β :=
--   (s.1.map f).fold op b


#check Set.union

#check Multiset.fold

#check Std.Commutative

-- #synth Std.Commutative Set.union

#check Commutative

--#synth Commutative Set.union

-- def finUnion {α : Type*} (B : Finset (Set α)) : Set α :=
--   B.fold (Set.union) ∅ id  -- why not working? why does mthalib not have an instance of `Std.Commutative`

--#check finUnion


#check Finset.range
open Finset in

theorem sum_range_id_mul_two' (n : ℕ) : (∑ i in range n, i) * 2 = n * (n - 1) :=
  calc
    (∑ i in range n, i) * 2 = (∑ i in range n, i) + ∑ i in range n, (n - 1 - i) := by
      rw [sum_range_reflect (fun i => i) n, mul_two]
    _ = ∑ i in range n, (i + (n - 1 - i)) := sum_add_distrib.symm
    _ = ∑ i in range n, (n - 1) :=
      sum_congr rfl fun i hi => add_tsub_cancel_of_le <| Nat.le_sub_one_of_lt <| mem_range.1 hi
    _ = n * (n - 1) := by rw [Finset.sum_const, card_range, Nat.nsmul_eq_mul]

open Finset in
theorem sum_cubes (n : ℕ) : (∑ i in range n, i^3) = (∑ i in range n, i)^2 := by
  obtain n := n
  · apply Nat.eq_of_mul_eq_mul_right (show 0 < 2^2 by norm_num)
    rw [←mul_pow, sum_range_id_mul_two]

    sorry

#exit

  apply nat.eq_of_mul_eq_mul_right (show 0 < 2^2, by norm_num),
  rw [←mul_pow, sum_range_id_mul_two],
  induction n with n ih, { simp },
  rw [finset.sum_range_succ, add_mul, ih],
  simp only [nat.succ_eq_add_one, nat.add_succ_sub_one, add_zero],
  ring



example : ∑ i : Fin 10, (3 - i) = 6 := by
  sorry
