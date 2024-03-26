import GameServer.Commands

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

import Game.Levels.Sum

import Game.Metadata.StructInstWithHoles

set_option tactic.hygienic false

World "Matrix"
Level 2

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


def first_column_sum_zero' {n : ℕ} [NeZero n] : Set (Matrix (Fin n) (Fin n) ℝ) :=
  fun A => ∑ i, A i 0 = 0

Statement FirstColumnSumZero'
    (preample := refine { carrier := M, ?..} <;> dsimp only)
    {n : ℕ} [NeZero n] :
    let M := {A : Matrix (Fin n) (Fin n) ℝ | ∑ i, A i 0 = 0}
    Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) := by
  Hint "Wir müssen jetzt die drei Axiome eines Untermoduls `S` zeigen:

  * Abgeschlossenheit unter `+`
  * Enthält `0`
  * Abgeschlossenheit unter `•`.

  Wir fangen mit dem ersten an:

  `intro A B hA hB`
  "
  · intro A B hA hB
    Hint (hidden := true) "
      A definitionally equal goal is `(∑ i, ({A} + {B}) i 0 ) = 0`.
      Tactic change can be used to change the goal to this.
      However, strictly speaking, this is not necessary since `simp` sees through such equalities."
    Branch
      change (∑ i, (A + B) i 0 ) = 0
    Hint (hidden := true) "`add_apply {A} {B}` simplifies the pointwise addition of two matrices."
    simp [add_apply A B]
    Hint (hidden := true) "`rw [sum_add_distrib]`"
    rw [sum_add_distrib]
    Hint (hidden := true) "`rw [{hA}, {hB}, zero_add]`"
    rw [hA, hB, zero_add]
  · Hint (hidden := true) "somwhat ugly…

    This is because `Submodule` consists of `AddSubmonoid` and `SubMulAction`.

    here we show that `0 ∈ (M, +)` as a submonoid.

    `simp`"
    simp
  · Hint "Oh god, is this ugly!

    similar reason as above, a simple `dsimp only` also brings this into a readably form

    `simp`"
    simp
    Hint "`intro c A hA`"
    intro c A hA
    Hint "`rw [← Finset.mul_sum]`"
    rw [← Finset.mul_sum]
    Hint "`rw [hA]`"
    rw [hA]
    Hint "`simp`"
    simp


  -- exact {
  -- carrier := {A | ∑ i, A i 0 = 0}
  -- add_mem' := by
  --   intro A B hA hB
  --   change (∑ i, (A + B) i 0 ) = 0
  --   simp [add_apply A B]
  --   rw [sum_add_distrib]
  --   rw [hA, hB, zero_add]
  -- zero_mem' := by
  --   simp
  -- smul_mem' := by
  --   simp
  --   intro c A hA
  --   rw [← Finset.mul_sum]
  --   rw [hA]
  --   simp }

NewTheorem Finset.mul_sum zero_add Finset.sum_add_distrib Matrix.add_apply
NewTactic change refine
