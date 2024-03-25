--import Game.Metadata
import GameServer.Commands

import Game.Levels.MatrixTrace.L01_VectorSpace
import Game.Levels.MatrixTrace.L02_SmulEBasis

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
  nth_rw 1 [matrix_eq_sum_std_basis A]
  simp_rw [map_sum]
  simp_rw [← smul_ebasis]
  simp_rw [LinearMap.map_smul]
  trans ∑ i : Fin n, ∑ j : Fin n, if i = j then (A i j) * f (E i j) else 0
  congr
  ext i
  congr
  ext j
  by_cases h₁ : i = j
  · rw [if_pos h₁]
    subst h₁
    rfl
  · rw [if_neg h₁]
    simp [h]
    right
    apply h
    assumption
  simp only [sum_ite_eq]
  simp only [sum_ite_mem]
  simp only [inter_self]
