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


lemma H4 {n : ℕ} {f : Matrix (Fin n.succ) (Fin n.succ) ℝ →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A)) (h₂ : f 1 = n.succ) :
    (n + 1) • f (E 0 0) = n + 1 := by
  have : (n + 1) • f (E 0 0) = f ( ((n + 1) : ℝ) • E 0 0) := by
    --unfold E
    rw [LinearMap.map_smul f]
    simp only [smul_eq_mul, nsmul_eq_mul]
    norm_cast
  rw [this]
  trans f (∑ _i : Fin (n + 1), E 0 0)
  · congr
    rw [Fin.sum_const (n + 1)]
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
      norm_cast

example {n : ℕ} [NeZero n] [AddCommMonoid A] (h : n * a = n * b)  : a = b := by
  apply?

--H5
lemma apple_ebasis_00 {n : ℕ} {f : Matrix (Fin n.succ) (Fin n.succ) ℝ →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A)) (h₂ : f 1 = n.succ) :
    f (E 0 0) = 1 := by
  apply mul_cancel

  rcases H4' h₁ h₂
  · assumption
  · exfalso
    apply succ_ne_zero n
    rw [succ_eq_add_one]
    rw [← cast_zero] at h
    apply Nat.cast_injective at h
    assumption
