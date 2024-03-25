--import Game.Metadata
import GameServer.Commands

import Game.Levels.MatrixTrace.L01_VectorSpace
import Game.Levels.MatrixTrace.L02_EBasisRescale

--import Game.StructInstWithHoles

set_option tactic.hygienic false

World "Trace"
Level 5

Title "Trace"

Introduction
"
A linear functional `f` on the space of `n × n` matrices (for non-zero `n`) which kills
all commutators and moreover satisfies `f(1) = n` has the property that `f (E i i) = 1`
for all `i : Fin n`.
"

open Nat Matrix BigOperators StdBasisMatrix Finset

lemma eq_sum_apply_diag_ebasis {n : ℕ} {f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ}
    (h : ∀ i j, i ≠ j → f (E i j) = 0)
    (A : Matrix _ _ ℝ) :
    f A = ∑ i : Fin n, (A i i) * f (E i i) := by
  rw [matrix_eq_sum_std_basis A]
  simp_rw [map_sum]
  simp_rw [← tmp1]
  simp_rw [LinearMap.map_smul]
  symm
  conv =>
    lhs
    simp only [E, stdBasisMatrix]
    simp only [sum_ite_eq, sum_ite_mem, inter_self]
  sorry



example [DecidableEq α] [AddCommMonoid β] (s : Finset α) (f : α → α → β) :
    ∑ i in s, ∑ j in s, (if i = j then f i j else 0) = ∑ i in s, f i i := by
  simp only [sum_ite_eq, sum_ite_mem, inter_self]


-- @[to_additive]
-- theorem prod_extend_by_one [DecidableEq α] (s : Finset α) (f : α → β) :
--     ∏ i in s, (if i ∈ s then f i else 1) = ∏ i in s, f i :=
--   (prod_congr rfl) fun _i hi => if_pos hi
-- #align finset.prod_extend_by_one Finset.prod_extend_by_one
-- #align finset.sum_extend_by_zero Finset.sum_extend_by_zero


  -- calc
  --   f A
  --   _ = f (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), (A i j) • E i j) := by
  --     congr
  --     simp_rw [tmp2]
  --     exact matrix_eq_sum_std_basis A
  --   _ = ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), (A i j) * f (E i j) := by
  --     rw [map_sum]
  --     simp_rw [map_sum, SMulHomClass.map_smul]
  --     rfl
  --   _ = ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), if i = j then (A i j) else 0 := by
  --     congr
  --     ext i
  --     congr
  --     ext j
  --     by_cases h : i = j
  --     · rw [if_pos h, h, H1 h₁, H5 h₁ h₂, mul_one]
  --     · rw [if_neg h, H2 h₁ i j h, mul_zero]
  --   _ = ∑ i : Fin (n + 1), (A i i) * f (E i i) := by
  --     congr
  --     ext i
  --     simp_rw [H1 h₁, H5 h₁ h₂, mul_one]
  --     simp
  --   _ = ∑ i : Fin (n + 1), (A i i) * f (E 0 0) := by simp_rw [H1 h₁]
  --   _ = f (E 0 0) * (∑ i : Fin (n + 1), (A i i)) := by rw [← Finset.sum_mul, mul_comm]
  --   _ = f (E 0 0) * trace A := by rfl
