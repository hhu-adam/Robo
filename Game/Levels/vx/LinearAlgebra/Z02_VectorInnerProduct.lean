--import Game.Metadata
import GameServer.Commands

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Matrix.Basic

import Game.Levels.Tmp.LinearAlgebra.Z01_Vector


import Game.StructInstWithHoles

set_option tactic.hygienic false

World "Matrix"
Level 2

Title "Matrix"

Introduction
"
The inner product (aka dot product) of vectors extends the notion of multiplication of numbers. Given two vectors `u : Fin m → ℝ` and `w : Fin m → ℝ` their inner product
`u ⬝ᵥ w` is a scalar given by the sum  `∑ i, u i * w i`.
"


open Matrix BigOperators

-- example : ![] ⬝ᵥ ![] = (![] : Fin 0 → ℝ) := by
--   simp [dotProduct]

example (u w : ℝ) : ![u] ⬝ᵥ ![w] = u * w := by
  simp only [dotProduct, Finset.univ_unique, Fin.default_eq_zero, cons_val_fin_one,
    Finset.sum_const, Finset.card_singleton, one_smul]

example (u₀ u₁ w₀ w₁ : ℝ) : ![u₀, u₁] ⬝ᵥ ![w₀, w₁] = u₀ * w₀ + u₁ * w₁ := by
  simp only [dotProduct, Fin.sum_univ_two, cons_val_zero, cons_val_one, head_cons]

example (u : ℝ) : ![1,-1] ⬝ᵥ ![u,u] = 0 := by
  simp only [dotProduct, Fin.sum_univ_two, cons_val_zero, one_mul, cons_val_one, head_cons, neg_mul,
    add_right_neg]

example {n : ℕ} (u : Fin n → ℝ) : 1 ⬝ᵥ u = ∑ i, u i := by
  simp only [dotProduct, Pi.one_apply, one_mul]

example (u₀ u₁ u₂ w₀ w₁ w₂ : ℝ) : ![u₀, u₁, 0] ⬝ᵥ ![0, w₁, w₂] = u₁ * w₁ := by
  simp [dotProduct]
  sorry

#check dotProduct_comm -- The inner product is symmetric

lemma dotProduct_nonneg {n : ℕ} (u : Fin n → ℝ) : 0 ≤ u ⬝ᵥ u := by
 sorry

lemma dotProduct_self_zero_iff_zero {n : ℕ} (u : Fin n → ℝ) : u ⬝ᵥ u = 0 ↔ u = 0 := by
  sorry

noncomputable
def norm {n : ℕ} (u : Fin n → ℝ) : ℝ := Real.sqrt (u ⬝ᵥ u)

-- Show that the inner product is linear in the first argument.
def innerProductLinear {n : ℕ} (u : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun := fun x => u ⬝ᵥ x
  map_add' := by
    intro x y
    simp only [dotProduct, Pi.add_apply]
    sorry
  map_smul' := by
    sorry


/-
Cauchy-Schwarz inequality?
-/
