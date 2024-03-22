--import Game.Metadata
import GameServer.Commands

import Game.Levels.MatrixTrace.L03_eBasisSpan

--import Game.StructInstWithHoles

set_option tactic.hygienic false

World "Trace"
Level 5

Title "Trace"

Introduction
"

"

open Nat Matrix BigOperators StdBasisMatrix

#check LinearMap.map_smul'
#check LinearMap.map_smul
#check Matrix.map_smul
#check Fin.sum_const





lemma H4 {n : ℕ} {f : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A)) (h₂ : f 1 = n.succ) :
    (n + 1) * f (E 0 0) = n + 1 := by
  have : ((n + 1) : ℝ) * f (E 0 0) = f ( ((n + 1) : ℝ) • E 0 0) := by
    --unfold E
    rw [LinearMap.map_smul f]
    simp only [smul_eq_mul]
  rw [this]
  trans f (∑ _i : Fin (n + 1), E 0 0)
  · congr
    rw [Fin.sum_const (n + 1)]
    simp only [smul_stdBasisMatrix]
    simp only [smul_eq_mul]
    simp only [mul_one]
    simp only [nsmul_eq_mul]
    simp only [cast_add, cast_one, mul_one]
  · sorry



  -- calc
  --   ↑(n + 1) * f (E 0 0)
  --   _ = f ((↑(n + 1) : ℝ) • E 0 0) := by exact LinearMap.map_smul' f ↑(n + 1) (E 0 0) |>.symm
  --   _ = f (∑ _i : Fin (n + 1) , E 0 0) := by
  --     congr
  --     rw [Fin.sum_const (n + 1)]
  --     simp
  --   _ = ∑ i : Fin (n + 1), f (E i i) := by
  --     rw [tmp3]
  --     congr
  --     ext i
  --     simp_rw [H1 h₁]
  --   _ = f (∑ i : Fin (n + 1), E i i) := by exact (map_sum f (fun x => E x x) Finset.univ).symm
  --   _ = f 1 := by rw [tmp1]
  --   _ = succ n := by rw [h₂]
  --   _ = ↑(n + 1) := by rw [succ_eq_add_one, cast_add, cast_one]


-- H5
-- lemma apple_ebasis_00 {n : ℕ} {f : Matrix (Fin n.succ) (Fin n.succ) ℝ →ₗ[ℝ] ℝ}
--     (h₁ : ∀ A B, f (A * B) = f (B * A)) (h₂ : f 1 = n.succ) :
--     f (E 0 0) = 1 := by
--   rcases H4' h₁ h₂
--   · assumption
--   · exfalso
--     apply succ_ne_zero n
--     rw [succ_eq_add_one]
--     rw [← cast_zero] at h
--     apply Nat.cast_injective at h
--     assumption
