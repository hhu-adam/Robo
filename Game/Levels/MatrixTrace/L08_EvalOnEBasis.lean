--import Game.Metadata
import GameServer.Commands

import Game.Levels.MatrixTrace.L06_EvalOnEBasis
import Game.Levels.MatrixTrace.L07_EvalOnEBasis

--import Game.StructInstWithHoles

set_option tactic.hygienic false

World "Matrix"
Level 10

Title "Matrix"

Introduction
"
A linear functional `f` on the space of `n × n` matrices (for non-zero `n`) which kills
all commutators and moreover satisfies `f(1) = n` has the property that `f (E i i) = 1`
for all `i : Fin n`.
"

open Nat Matrix BigOperators StdBasisMatrix

#check NeZero

Statement one_on_diag_ebasis {n : ℕ} {f : Matrix (Fin n.succ) (Fin n.succ) ℝ →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A)) (h₂ : f 1 = n.succ) :
    ∀ i, f (E i i) = 1 := by
  intro i
  apply nat_mul_inj'
  have : n.succ * f (E i i) = f ( (n.succ : ℝ) • E i i) := by
    --unfold E
    rw [LinearMap.map_smul f]
    simp only [smul_eq_mul]
  rw [this]
  trans f (∑ _i : Fin n.succ, E i i)
  · congr
    rw [Fin.sum_const n.succ]
    simp only [smul_stdBasisMatrix]
    simp only [smul_eq_mul]
    simp only [mul_one]
    simp only [nsmul_eq_mul]
    simp only [cast_add, cast_one, mul_one]
  · rw [map_sum f (fun x => E i i) Finset.univ]
    --rw [apply_ebasis_diag h₁]
    trans ∑ i : Fin n.succ, f (E i i)
    · congr
      ext j
      simp only [eq_on_diag_ebasis  h₁ i j]
    · rw [← map_sum f (fun x => E x x) Finset.univ]
      rw [ebasis_diag_sum_eq_one]
      simp only [h₂]
      simp
  simp
