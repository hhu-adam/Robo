--import Game.Metadata
import GameServer.Commands

import Game.Levels.MatrixTrace.L06_EqOnDiagEBasis
import Game.Levels.MatrixTrace.L07_ZeroOnOffDiagEBasis

--import Game.StructInstWithHoles

set_option tactic.hygienic false

World "Trace"
Level 7

Title "Trace"

Introduction
"
A linear functional `f` on the space of `n × n` matrices (for non-zero `n`) which kills
all commutators and moreover satisfies `f(1) = n` has the property that `f (E i i) = 1`
for all `i : Fin n`.
"

open Nat Matrix BigOperators StdBasisMatrix

lemma one_on_diag_ebasis {n : ℕ} {f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A)) (h₂ : f 1 = n) :
    ∀ i, n * f (E i i) = n := by
  intro i
  have : n * f (E i i) = f ( (n : ℝ) • E i i) := by
    --unfold E
    rw [LinearMap.map_smul f]
    simp only [smul_eq_mul]
  rw [this]
  trans f (∑ _i : Fin n, E i i)
  · congr
    rw [Fin.sum_const n]
    simp only [smul_stdBasisMatrix]
    simp only [smul_eq_mul]
    simp only [mul_one]
    simp only [nsmul_eq_mul]
    simp only [cast_add, cast_one, mul_one]
  · rw [map_sum f (fun x => E i i) Finset.univ]
    --rw [apply_ebasis_diag h₁]
    trans ∑ i : Fin n, f (E i i)
    · congr
      ext j
      simp only [eq_on_diag_ebasis_of_zero_on_commutator  h₁ i j]
    · rw [← map_sum f (fun x => E x x) Finset.univ]
      rw [ebasis_diag_sum_eq_one]
      simp only [h₂]

lemma tmp7 {n : ℕ} {f : Matrix (Fin n.succ) (Fin n.succ) ℝ →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A)) (h₂ : f 1 = n.succ) :
    f (E 0 0) = 1 := by
  apply nat_mul_inj'
  · rw [mul_one]
    apply one_on_diag_ebasis h₁ h₂
  · exact succ_ne_zero n
