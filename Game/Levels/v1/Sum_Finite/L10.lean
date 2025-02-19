import Game.Metadata

World "Finite"
Level 10

Title "" -- "Gauss Sum"

Introduction
"

"

open Finset BigOperators


#check sum_congr
#check add_tsub_cancel_of_le


-- theorem sum_antidiagonal_eq (n : ℕ) (f : ℕ × ℕ → ℕ) :
--   ∑ p in nat.antidiagonal n, f p = ∑ i in range (n + 1), f (i, n - i) :=
-- begin
--   rw [nat.antidiagonal_eq_image, sum_image], simp,
--   intros; assumption
-- end

-- theorem sum_antidiagonal_eq' (n : ℕ) (f : ℕ × ℕ → ℕ) :
--    ∑ p in nat.antidiagonal n, f p = ∑ i : fin n.succ, f(↑i, n - ↑i) :=
-- by rw [sum_antidiagonal_eq, finset.sum_range]


#check Nat.le_sub_one_of_lt

-- `range` is monotone.
Statement le_range_subset {m n} :  n ≤ m → range n ⊆ range m := by
  -- simp
  intro h x hx
  Branch
    simp only [mem_range] at *
    linarith
  simp at *
  linarith

Statement two : 2 ∈ range 3 := by
  -- simp
  simp only [mem_range]
  simp only [Nat.lt_succ_self]

Statement three : 3 ∉ range 3 := by
  simp only [mem_range]
  --simp
  simp only [lt_self_iff_false]
  simp only [not_false_eq_true]

Statement {m n k : ℕ} : m ∈ range n → k ≤ m → k ∈ range n := by
  intro h₁ h₂
  simp at *
  linarith


-- Statement lt_range_subset {m n} :  n < m + 1 → range n ⊆ range m := by
--   intro h
--   simp at *


Statement range_union {m n} : range m ∪ range n = range (max m n) := by
  ext x
  Branch
    simp only [mem_union, mem_range, lt_max_iff]
  simp

Statement range_inter {m n} : range m ∩ range n = range (min m n) := by
  aesop

#check @range

Statement sum_range_id_mul_two (n : ℕ) :
    (∑ i in range n, i) * 2 = n * (n - 1) := by
  trans (∑ i in range n, i) + ∑ i in range n, (n - 1 - i)
  · rw [sum_range_reflect (fun i => i) n]
    rw [mul_two]
  · trans ∑ i in range n, (i + (n - 1 - i))
    · rw [sum_add_distrib]
    · trans ∑ i in range n, (n - 1)
      · apply sum_congr
        · rfl
        · intro i hi
          apply add_tsub_cancel_of_le
          apply Nat.le_sub_one_of_lt
          simpa [mem_range] using hi
      · simp


theorem headless  : ¬ ∃ f : Multiset ℕ → ℕ, ∀ l : List ℕ, ∀ (h : l ≠ []), f l = l.head h := by
  push_neg
  intro f
  have h₀ : @Multiset.ofList ℕ [1, 2] = @Multiset.ofList ℕ [2, 1] := by
    apply Multiset.pair_comm
  by_cases h: f [1, 2] = 1
  · use [2, 1], List.cons_ne_nil _ _
    rw [← h₀, h]
    simp
  · use [1, 2], List.cons_ne_nil _ _
    contrapose h
    simp at *
    assumption

#check Submodule.exists_le_ker_of_lt_top

variable {X : Type}

example {x i : X} (h : i ∈ ({x} : Set X)) : i = x := by
  apply Set.mem_singleton_iff.1 h

-- TODO: push this to mathlib
example {x i : X} (h : i ∉ ({x} : Set X)) : i ≠ x := by
  contrapose! h
  apply Set.mem_singleton_iff.1 h

@[simp]
theorem not_mem_singleton_iff {a b : X} : a ∉ ({b} : Set X) ↔ a ≠ b :=
  Iff.rfl



--#check contrapose


#check Set.singleton
