-- import Game.Metadata
import GameServer.Commands

import Game.Levels.MatrixTrace.L05_LinMapApplyeBasisDiag
import Game.Levels.MatrixTrace.L06_LinMapApplyeBasisOffDiag


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

/- Statements about linear maps and sums. -/

lemma tmp3 {n m : ℕ}
    (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    f (∑ _i : Fin m, A) = ∑ _i : Fin m, f A := by
  exact map_sum f (fun _x => A) Finset.univ

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
