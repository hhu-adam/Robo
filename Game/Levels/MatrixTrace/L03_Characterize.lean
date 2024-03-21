--import Game.Metadata
import GameServer.Commands

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Trace

--import Game.StructInstWithHoles

set_option tactic.hygienic false

World "Trace"
Level 3 -- boss level

Title "Trace"

Introduction
"
The trace of as a map from the space of `n × n` matrices to the field of scalars has the following properties:
1. It is linear, witnessed by `traceLinear`.
2. The trace of a identity matrix is the dimension of the matrix, i.e.
`trace (1 : Matrix α α ℝ) = Fintype.card α`.
3. The matrices in the trace of a product can be switched without changing the result, i.e. `trace (A * B) = trace (B * A)`. This is witnessed by `trace_mul_comm`.

We show that these properties characterize the trace, that is any map satisfying these properties is equal to the trace.
"

open Matrix BigOperators StdBasisMatrix

#check Matrix

#check stdBasisMatrix

#check StdBasisMatrix.mul_right_apply_same

#check trace_mul_comm

abbrev E {n : ℕ} (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  stdBasisMatrix i j 1

lemma trace_eq_one {i : Fin n} : trace (E i i) = 1 := by
  simp only [trace_eq]

lemma E_mul_E {n : ℕ} {i j k : Fin n} : E i j * E j k = E i k := by
  simp only [mul_same, mul_one]

lemma E_mul_E_ne {i j k l : Fin n} (h : j ≠ k) :
    E i j * E k l = 0 := by
  exact mul_of_ne i j 1 h 1

theorem linearMap_eq_trace {n : ℕ} (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ) (h₁ : ∀ A B, f (A * B) = f (B * A)) (h₂ : f 1 = n) : f.toFun = trace := by
  ext A
  cases n with
  | zero =>
    simp [trace_eq_zero_of_isEmpty]
    have : A = 0 := by
      apply Subsingleton.elim
    simp only [this, f.map_zero]
  | succ n =>
    have H1 : ∀ (j : Fin (n + 1)),  f (E j j) = f (E 0 0) := by
      intro j
      calc
        f (E j j) = f (E j 0 * E 0 j) := by rw [mul_same, mul_one]
        _ = f (E 0 j * E j 0) := by rw [h₁]
        _ = f (E 0 0) := by rw [mul_same, mul_one]
    have H2 : ∀ (i j : Fin (n + 1)), (i ≠ j) → f (E i j) = 0 := by
      intro i j hne
      calc
        f (E i j) = f (E i 0 * E 0 j) := by rw [mul_same, mul_one]
        _ = f (E 0 j * E i 0) := by rw [h₁]
        _ = f (0) := by rw [mul_of_ne 0 j 1 hne.symm 1] -- rw [E_mul_E_ne hne.symm]
        _ = 0 := by simp only [map_zero]
    have H3 : f (A) = f (E 0 0) * trace A := by
      calc
        f (A) = f (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), (A i j) • E i j) := by sorry
        _ = ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), (A i j) * f (E i j) := by
          rw [map_sum]
          simp_rw [map_sum, SMulHomClass.map_smul]
          rfl
        _ = ∑ i : Fin (n + 1), (A i i) * f (E i i) := by sorry
        _ = ∑ i : Fin (n + 1), (A i i) * f (E 0 0) := by simp_rw [H1]
        _ = f (E 0 0) * trace A := by sorry --Finset.sum_mul_distrib
    have H4 : (n + 1) * f (E 0 0) = n + 1 := by
      calc
        (n + 1) * f (E 0 0) = f ((n + 1) • E 0 0) := by sorry
        _ = f (∑ i : Fin (n + 1) , E 0 0) := by sorry
        _ = ∑ i : Fin (n + 1), f (E i i) := by sorry
        _ = f (∑ i : Fin (n + 1), E i i) := by sorry
        _ = f (1) := by sorry
        _ = n + 1 := by sorry
    have H5 : f (E 0 0) = 1 := by
      sorry
    simp [H5] at H3
    assumption
