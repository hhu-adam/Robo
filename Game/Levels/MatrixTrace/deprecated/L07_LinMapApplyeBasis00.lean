--import Game.Metadata
import GameServer.Commands

import Game.Levels.MatrixTrace.L05_LinMapApplyeBasisDiag
import Game.Levels.MatrixTrace.L06_LinMapApplyeBasisOffDiag

--import Game.StructInstWithHoles

set_option tactic.hygienic false

World "Trace"
Level 7

Title "Trace"

Introduction
"

"

open Nat Matrix BigOperators StdBasisMatrix


lemma apply_ebasis_00 {n : ℕ} {f : Matrix (Fin n.succ) (Fin n.succ) ℝ →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A)) (h₂ : f 1 = n.succ) :
    n.succ * f (E 0 0) = n.succ := by
  have : n.succ * f (E 0 0) = f ( (n.succ : ℝ) • E 0 0) := by
    --unfold E
    rw [LinearMap.map_smul f]
    simp only [smul_eq_mul]
  rw [this]
  trans f (∑ _i : Fin n.succ, E 0 0)
  · congr
    rw [Fin.sum_const n.succ]
    simp only [smul_stdBasisMatrix]
    simp only [smul_eq_mul]
    simp only [mul_one]
    simp only [nsmul_eq_mul]
    simp only [cast_add, cast_one, mul_one]
  · rw [map_sum f (fun x => E 0 0) Finset.univ]
    --rw [apply_ebasis_diag h₁]
    trans ∑ i : Fin (n + 1), f (E i i)
    · congr
      ext i
      simp only [apply_ebasis_diag h₁]
    · rw [← map_sum f (fun x => E x x) Finset.univ]
      rw [ebasis_diag_sum_eq_one]
      simp only [h₂]



#check nat_mul_inj'
#check Nat.cast_injective

example {n : ℕ} [NeZero n] (a : ℝ) (h : n * a = n)  : a = 1 := by
  rw [nat_mul_inj' (h.trans (mul_one (n : ℝ)).symm)]
  exact NeZero.ne n

lemma tmp7 {n : ℕ} {f : Matrix (Fin n.succ) (Fin n.succ) ℝ →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A)) (h₂ : f 1 = n.succ) :
    f (E 0 0) = 1 := by
  apply nat_mul_inj' (n:= n.succ)
  · rw [mul_one]
    apply apply_ebasis_00 h₁ h₂
  · exact succ_ne_zero n
