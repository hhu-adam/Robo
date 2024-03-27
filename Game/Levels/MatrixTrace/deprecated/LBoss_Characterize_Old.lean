-- import Game.Metadata
import GameServer.Commands

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Trace

import Mathlib

notation R"^("n"×"m")" => Matrix (Fin n) (Fin m) R

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

/- Statements about `E` -/

-- lemma trace_eq_one {n : ℕ} {i : Fin n} : trace (E i i) = 1 := by
--   simp only [trace_eq]

-- lemma E_mul_E {n : ℕ} {i j k : Fin n} : E i j * E j k = E i k := by
--   simp only [mul_same, mul_one]

-- lemma E_mul_E_ne {n : ℕ} {i j k l : Fin n} (h : j ≠ k) :
--     E i j * E k l = 0 := by
--   exact mul_of_ne i j 1 h 1

lemma tmp0 {n : ℕ} {i : Fin n} :
    E i i = stdBasisMatrix i i ((1 : Matrix (Fin n) (Fin n) ℝ) i i) := by
  rw [one_apply_eq]

lemma tmp1 {n : ℕ} : ∑ i : Fin (n), E i i = 1 := by
  unfold E
  rw [matrix_eq_sum_std_basis (1 : Matrix (Fin n) (Fin n) ℝ)]
  simp_rw [tmp0]
  symm
  calc ∑ i : Fin n, ∑ j : Fin n, stdBasisMatrix i j ((1 : Matrix (Fin n) (Fin n) ℝ) i j)
  _ = ∑ i : Fin n, ∑ j : Fin n, stdBasisMatrix i j (if i = j then 1 else 0) := rfl
  _ = ∑ i : Fin n, ∑ j : Fin n, (if i = j then stdBasisMatrix i j 1 else 0) := by
    congr
    funext i
    congr
    funext j
    split
    · simp
    · simp
  _ = ∑ i : Fin n, stdBasisMatrix i i 1 := by simp
  _ = ∑ x : Fin n, stdBasisMatrix x x ((1 : Matrix (Fin n) (Fin n) ℝ) x x) := by simp

lemma tmp2 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j) :
    A i j • E i j = stdBasisMatrix i j (A i j) := by
  simp_all only [smul_stdBasisMatrix, smul_eq_mul, mul_one]

/- Statements about linear maps and sums. -/

lemma tmp3 {n m : ℕ}
    (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    f (∑ _i : Fin m, A) = ∑ _i : Fin m, f A := by
  exact map_sum f (fun _x => A) Finset.univ

/- Exercises specific about our `f` -/

lemma H1 {n : ℕ} {f : Matrix (Fin n.succ) (Fin n.succ) ℝ →ₗ[ℝ] ℝ}
    (h : ∀ A B, f (A * B) = f (B * A)) (j : Fin n.succ) :
    f (E j j) = f (E 0 0) := by
  trans f (E j 0 * E 0 j)
  · rw [mul_same, mul_one]
  · rw [h, mul_same, mul_one]

lemma H2 {n : ℕ} {f : Matrix (Fin n.succ) (Fin n.succ) ℝ →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A)) :
    ∀ (i j :
     Fin (n + 1)), (i ≠ j) → f (E i j) = 0 := by
  intro i j hne
  trans f (E i 0 * E 0 j)
  · rw [mul_same, mul_one]
  · rw [h₁]
    rw [mul_of_ne 0 j 1 hne.symm 1] -- rw [E_mul_E_ne hne.symm]
    simp

lemma H4 {n : ℕ} {f : Matrix (Fin n.succ) (Fin n.succ) ℝ →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A)) (h₂ : f 1 = n.succ) :
    (↑(n + 1) : ℝ) * f (E 0 0) = (↑(n + 1) : ℝ) := by
  calc
    ↑(n + 1) * f (E 0 0)
    _ = f ((↑(n + 1) : ℝ) • E 0 0) := by exact LinearMap.map_smul' f ↑(n + 1) (E 0 0) |>.symm
    _ = f (∑ _i : Fin (n + 1) , E 0 0) := by
      congr
      rw [Fin.sum_const (n + 1)]
      simp
    _ = ∑ i : Fin (n + 1), f (E i i) := by
      rw [tmp3]
      congr
      ext i
      simp_rw [H1 h₁]
    _ = f (∑ i : Fin (n + 1), E i i) := by exact (map_sum f (fun x => E x x) Finset.univ).symm
    _ = f 1 := by rw [tmp1]
    _ = succ n := by rw [h₂]
    _ = ↑(n + 1) := by rw [succ_eq_add_one, cast_add, cast_one]

lemma H4' {n : ℕ} {f : Matrix (Fin n.succ) (Fin n.succ) ℝ →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A)) (h₂ : f 1 = n.succ) :
    f (E 0 0) = 1 ∨ (↑(n + 1) : ℝ) = 0 := by
  have H4' := H4 h₁ h₂
  nth_rw 2 [← mul_one (↑(n + 1) : ℝ)] at H4'
  rw [mul_eq_mul_left_iff] at H4'
  assumption

lemma H5 {n : ℕ} {f : Matrix (Fin n.succ) (Fin n.succ) ℝ →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A)) (h₂ : f 1 = n.succ) :
    f (E 0 0) = 1 := by
  rcases H4' h₁ h₂
  · assumption
  · exfalso
    apply succ_ne_zero n
    rw [succ_eq_add_one]
    rw [← cast_zero] at h
    apply Nat.cast_injective at h
    assumption

lemma H3 {n : ℕ} {f : Matrix (Fin n.succ) (Fin n.succ) ℝ →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A)) (h₂ : f 1 = n.succ)
    (A : Matrix _ _ ℝ) :
    f A = f (E 0 0) * trace A := by
  calc
    f A
    _ = f (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), (A i j) • E i j) := by
      congr
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
      · rw [if_pos h, h, H1 h₁, H5 h₁ h₂, mul_one]
      · rw [if_neg h, H2 h₁ i j h, mul_zero]
    _ = ∑ i : Fin (n + 1), (A i i) * f (E i i) := by
      congr
      ext i
      simp_rw [H1 h₁, H5 h₁ h₂, mul_one]
      simp
    _ = ∑ i : Fin (n + 1), (A i i) * f (E 0 0) := by simp_rw [H1 h₁]
    _ = f (E 0 0) * (∑ i : Fin (n + 1), (A i i)) := by rw [← Finset.sum_mul, mul_comm]
    _ = f (E 0 0) * trace A := by rfl

lemma H3' {n : ℕ} {f : Matrix (Fin n.succ) (Fin n.succ) ℝ →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A)) (h₂ : f 1 = n.succ)
    (A : Matrix _ _ ℝ) : f A = trace A := by
  have H := H3 h₁ h₂ A
  simp [H5 h₁ h₂] at H
  assumption

/- The Statement -/

Statement {n : ℕ} (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ)
    (h₁ : ∀ A B, f (A * B) = f (B * A)) (h₂ : f 1 = n) :
    ↑f = trace := by
  ext A
  rcases n
  · simp
    rw [← f.map_zero]
    congr
    -- there is apparently exactly one 0×0-matrix
    apply Subsingleton.elim
  · exact H3' h₁ h₂ A
