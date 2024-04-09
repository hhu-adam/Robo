import Game.Metadata
import Game.Metadata.StructInstWithHoles

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

import Game.Levels.Sum


World "Matrix"
Level 1

Title "Matrix"

Introduction
"
The collection `ℝ^(m×n)` of `m × n` matrices with real-valued entries forms a vector space over `ℝ`.
In this level you prove that for `n > 0` the collection of square matrices of size `n × n` with the property that the sum of whose first column is zero forms a subspace of `ℝ^(n×n)`.

In Lean we provide a submodule structure by filling in the holes of the following structure:
```
def FirstColumnSumZero {n : ℕ} [NeZero n] :
    Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {A | ∑ i, A i 0 = 0}
  add_mem' := sorry
  zero_mem' := sorry
  smul_mem' := sorry
```
"

/-- Short notation for `n x m`-Matrices.

Careful: not tested well! use the official notation
`Matrix (Fin n) (Fin m) R` if it does not work. -/
notation (name := concreteMatrix) "Mat["n","m"]["R"]" => Matrix (Fin n) (Fin m) R

open Nat Matrix BigOperators StdBasisMatrix Finset

-- Bemerkungen:
-- 1) An m×n matrix with entries in `ℝ` is a function `Fin m → Fin n → ℝ`.
-- 2) The type of m×n matrices with entries in `ℝ` is `Matrix (Fin m) (Fin n) ℝ`.
-- 3) We use the notatoin `ℝ^(m×n)` for `Matrix (Fin m) (Fin n) ℝ` since it has better compatibility with the column-vector and row-vector matrices.
-- 4) The empty square matrix is the unique function `Fin 0 → Fin 0 → ℝ`.


-- def first_column_sum_zero {n : ℕ} [NeZero n] : Set (Matrix (Fin n) (Fin n) ℝ) :=
--   fun A => ∑ i, A i 0 = 0

Statement FirstColumnSumZero
    (preamble := refine { carrier := M, ?..} <;> dsimp only)
    {n : ℕ} [NeZero n] :
    let M := {A : Matrix (Fin n) (Fin n) ℝ | ∑ i, A i 0 = 0}
    Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) := by
  Hint "**Du**: Robo, kannst du mir helfen?

  **Robo**: Klar, den Untervektorraum kann ich definieren, aber ich verstehe die Mathe nicht.
  Hier sind die drei Goals die noch übrig sind.
  "
  · Hint "**Du**: Ich verstehe, beim ersten müssen wir zeigen, dass `a + b` wieder in `M` ist."
    intro A B hA hB
    Hint (hidden := true) "
      A definitionally equal goal is `(∑ i, ({A} + {B}) i 0 ) = 0`.
      Tactic `change` can be used to change the goal to this.
      However, strictly speaking, this is not necessary since `simp` sees through such equalities."
    Branch
      change (∑ i, (A + B) i 0 ) = 0
    Hint (hidden := true) "`add_apply {A} {B}` simplifies the pointwise addition of two matrices."
    simp [add_apply A B]
    Hint (hidden := true) "`rw [sum_add_distrib]`"
    rw [sum_add_distrib]
    Hint (hidden := true) "`rw [{hA}, {hB}, zero_add]`"
    rw [hA, hB, zero_add]
  · Hint "**Robo**: Dieses Goal verlangt, dass `0` in `M` liegt."
    simp
  · Hint "**Du**: Ah und das letzte Goal will dass `r • a` in `M` liegt!

    **Robo**: sieht ganz so aus!"
    Hint "`simp`"
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

TheoremTab "Matrix"
