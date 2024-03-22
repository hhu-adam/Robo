import GameServer.Commands

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

import Game.Levels.Sum

import Game.Metadata.StructInstWithHoles

set_option tactic.hygienic false

notation R"^("n"×"m")" => Matrix (Fin n) (Fin m) R

World "Matrix"
Level 1

Title "Matrix"

Introduction
"
The collection `ℝ^(m×n)` of `m × n` matrices with real-valued entries forms a vector space over `ℝ`.
In this level you prove that for `n > 0` the collection of square matrices of size `n × n` with the property that the sum of whose first column is zero forms a subspace of `ℝ^(n×n)`.
"

open Nat Matrix BigOperators StdBasisMatrix Finset

-- Bemerkungen:
-- 1) An m×n matrix with entries in `ℝ` is a function `Fin m → Fin n → ℝ`.
-- 2) The type of m×n matrices with entries in `ℝ` is `Matrix (Fin m) (Fin n) ℝ`.
-- 3) We use the notatoin `ℝ^(m×n)` for `Matrix (Fin m) (Fin n) ℝ` since it has better compatibility with the column-vector and row-vector matrices.
-- 4) The empty square matrix is the unique function `Fin 0 → Fin 0 → ℝ`.


def first_column_sum_zero {n : ℕ} [NeZero n] : Set (Matrix (Fin n) (Fin n) ℝ) :=
  fun A => ∑ i, A i 0 = 0

def FirstColumnSumZero {n : ℕ} [NeZero n] : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {A | ∑ i, A i 0 = 0}
  add_mem' := by
    intro A B hA hB
    change (∑ i, (A + B) i 0 ) = 0
    simp [add_apply A B]
    rw [sum_add_distrib]
    rw [hA, hB, zero_add]
  zero_mem' := by
    simp
  smul_mem' := by
    simp
    intro c A hA
    rw [← Finset.mul_sum]
    rw [hA]
    simp
