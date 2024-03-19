import GameServer.Commands

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
-- import Mathlib.Data.FinSet
import Game.Levels.Sum

import Game.StructInstWithHoles

set_option tactic.hygienic false

World "Matrix"
Level 1

Title "Matrix"

Introduction
"
The collection of `m × n` matrices with real-valued entries forms a vector space over `ℝ`.
"

-- Bemerkungen:
-- 1) An m×n matrix with entries in `ℝ` is a function `Fin m → Fin n → ℝ`.
-- 2) The type of m×n matrices with entries in `ℝ` is `matrix (Fin m) (Fin n) ℝ`.
-- 3) The empty square matrix is the unique function `Fin 0 → Fin 0 → ℝ`.
-- 4) Given a square matrix `A` of size `n × n`, the diagonal `diag A` is a vector `n → α` such that `(diag A) i = A i i`.
-- 5) Given a square matrix `A` of size `n × n`, the trace `tr A` is the sum of the diagonal entries of `A`.

#check Pi.mulAction

set_option trace.Meta.synthInstance true


-- we should not need noncomputable here but it seems Lean is using an instance of RorC through the inner product instance here.
noncomputable
instance (n : ℕ) : Module ℝ (Matrix (Fin n) (Fin n) ℝ) := by infer_instance

#check Matrix.module

#synth Module ℝ (Matrix (Fin n) (Fin n) ℝ)



-- Remark: maybe we should introduce `funext` or `ext` before if we have not done so.
instance (n : ℕ) : Module ℝ (Matrix (Fin n) (Fin n) ℝ) where
  smul := fun r A i j => r * A i j --r • A i j  -- Pi.instSMul
  one_smul := by -- simp
    intro A
    funext i j
    dsimp
    rw [one_mul] --?
  mul_smul := by
    intro x y A
    funext i j
    dsimp
    rw [mul_assoc] --?
  smul_zero := by
    intro r
    funext i j
    dsimp
    rw [mul_zero] --?
  smul_add := by
    intro r A B
    funext i j
    dsimp
    rw [mul_add] --?
  add_smul := by
    intro r s A
    funext i j
    dsimp
    rw [add_mul] --?
  zero_smul := by
    intro A
    funext i j
    dsimp
    rw [zero_mul] --?


-- Use L01_Module to show that `n × n` matrices with real-valued entries form a module over `ℚ`.
instance (n : ℕ) : Module ℚ (Matrix (Fin n) (Fin n) ℝ) where
