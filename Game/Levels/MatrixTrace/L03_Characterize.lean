-- import Game.Metadata
import GameServer.Commands

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Trace

import Mathlib

notation R"^"n" × "m => Matrix (Fin n) (Fin m) R

World "Trace"
Level 1

Title "Trace"

Introduction
"
The trace as a map from the space of `n × n` matrices to the field of scalars has the following properties:
1. It is linear, witnessed by `traceLinear`.
2. The trace of a identity matrix is the dimension of the matrix, i.e.
`trace (1 : Matrix α α ℝ) = Fintype.card α`.
3. The matrices in the trace of a product can be switched without changing the result, i.e. `trace (A * B) = trace (B * A)`. This is witnessed by `trace_mul_comm`.

We show that these properties characterize the trace, that is any map satisfying these properties is equal to the trace.
"

open Nat Matrix BigOperators StdBasisMatrix

set_option relaxedAutoImplicit false
set_option autoImplicit false

#check Matrix

#check stdBasisMatrix

#check StdBasisMatrix.mul_right_apply_same

#check trace_mul_comm

abbrev E {n : ℕ} (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  stdBasisMatrix i j 1

lemma trace_eq_one {n : ℕ} {i : Fin n} : trace (E i i) = 1 := by
  simp only [trace_eq]

lemma E_mul_E {n : ℕ} {i j k : Fin n} : E i j * E j k = E i k := by
  simp only [mul_same, mul_one]

lemma E_mul_E_ne {n : ℕ} {i j k l : Fin n} (h : j ≠ k) :
    E i j * E k l = 0 := by
  exact mul_of_ne i j 1 h 1

lemma tmp1 {n : ℕ} : ∑ i : Fin (n + 1), E i i = 1 := by sorry

lemma tmp2 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j) :
    A i j • E i j = stdBasisMatrix i j (A i j) := by sorry

lemma tmp3 {n m : ℕ}
    (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    f (∑ _i : Fin m, A) = ∑ _i : Fin m, f A := by
  exact map_sum f (fun _x => A) Finset.univ

-- lemma tmp4 {n : ℕ} {A : Type} (a : A) [AddCommMonoid A] [Module ℝ A] : ∑ i : Fin (n + 1), a = (n + 1) • a := by
--   exact Fin.sum_const (n + 1) a

Statement linearMap_eq_trace {n : ℕ} (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ)
    (h₁ : ∀ A B, f (A * B) = f (B * A)) (h₂ : f 1 = n) :
    ↑f = trace := by
  funext A
  rcases n
  · simp
    have hA : A = 0 := by
      apply Subsingleton.elim
    rw [hA, f.map_zero]
  · have H5 : f (E 0 0) = 1 := by
      sorry
    have H6 : ∀ i j, i ≠ j → f (E i j) = 0 := by
      -- is this true?
      sorry
    have H1 : ∀ (j : Fin (n + 1)),  f (E j j) = f (E 0 0) := by
      intro j
      calc
        f (E j j)
        _ = f (E j 0 * E 0 j) := by rw [mul_same, mul_one]
        _ = f (E 0 j * E j 0) := by rw [h₁]
        _ = f (E 0 0) := by rw [mul_same, mul_one]
    have H2 : ∀ (i j : Fin (n + 1)), (i ≠ j) → f (E i j) = 0 := by
      intro i j hne
      calc
        f (E i j)
        _ = f (E i 0 * E 0 j) := by rw [mul_same, mul_one]
        _ = f (E 0 j * E i 0) := by rw [h₁]
        _ = f (0) := by rw [mul_of_ne 0 j 1 hne.symm 1] -- rw [E_mul_E_ne hne.symm]
        _ = 0 := by simp only [map_zero]
    have H3 : f (A) = f (E 0 0) * trace A := by
      calc
        f (A)
        _ = f (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), (A i j) • E i j) := by
          apply congrArg
          simp_rw [tmp2]
          exact matrix_eq_sum_std_basis A
        _ = ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), (A i j) * f (E i j) := by
          rw [map_sum]
          simp_rw [map_sum, SMulHomClass.map_smul]
          rfl
        _ = ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), if i = j then (A i j) else 0 := by
          congr
          ext i
          congr
          ext j
          by_cases h : i = j
          · rw [if_pos h, h, H1, H5, mul_one]
          · rw [if_neg h, H6 i j h, mul_zero]
        _ = ∑ i : Fin (n + 1), (A i i) * f (E i i) := by
          congr
          ext i
          simp_rw [H1, H5, mul_one]
          simp
        _ = ∑ i : Fin (n + 1), (A i i) * f (E 0 0) := by simp_rw [H1]
        _ = f (E 0 0) * (∑ i : Fin (n + 1), (A i i)) := by rw [← Finset.sum_mul, mul_comm]
        _ = f (E 0 0) * trace A := by rfl
    have H4 : (↑(n + 1) : ℝ) * f (E 0 0) = n + 1 := by
            calc
        ↑(n + 1) * f (E 0 0)
        _ = f ((↑(n + 1) : ℝ) • E 0 0) := by exact LinearMap.map_smul' f ↑(n + 1) (E 0 0) |>.symm
        _ = f (∑ i : Fin (n + 1) , E 0 0) := by
          congr
          rw [Fin.sum_const (n + 1)]
          simp
        _ = ∑ i : Fin (n + 1), f (E i i) := by
          rw [tmp3]
          congr
          ext i
          simp_rw [H1]
        _ = f (∑ i : Fin (n + 1), E i i) := by exact (map_sum f (fun x => E x x) Finset.univ).symm
        _ = f 1 := by rw [tmp1]
        _ = succ n := by rw [h₂]
        _ = n + 1 := by rw [succ_eq_add_one, cast_add, cast_one]
    simp [H5] at H3
    assumption
