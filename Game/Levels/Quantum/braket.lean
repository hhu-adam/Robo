import Game.Metadata
import Game.Levels.Sum

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
-- import Mathlib.Data.Complex.RorC
import Game.Levels.MatrixTrace

World "Quantum"
Level 1

Title "Braket"

Introduction
"

"

open Nat Matrix BigOperators

#check stdBasisMatrix
variable {K V : Type _} [Field K]

@[simp]
def ket0 : Fin 2 → K := ![1 ,0]

@[simp]
def ket1 : Fin 2 → K := ![0,1]


@[simp]
def ket00 : Fin 4 → K := ![1,0,0,0]

@[simp]
def ket01 : Fin 4 → K := ![0,1,0,0]

@[simp]
def ket10 : Fin 4 → K := ![0,0,1,0]

@[simp]
def ket11 : Fin 4 → K := ![0,0,0,1]

notation "|0⟩" => ket0
notation "|1⟩" => ket1

notation "|00⟩" => ket00
notation "|01⟩" => ket01
notation "|10⟩" => ket10
notation "|11⟩" => ket11

notation "√2" => Real.sqrt 2

noncomputable
def ket_plus : Fin 2 → ℝ := ![√2/2, √2/2]

noncomputable
def ket_minus : Fin 2 → ℝ := ![√2/2, -√2/2]

notation "|+⟩" => ket_plus
notation "|-⟩" => ket_minus

@[simp]
def amplitude_squared {n : ℕ} (v : Fin n → ℝ) := ∑ i : Fin n, (v i)^2

theorem amplitude_squared_ket0 : amplitude_squared |0⟩ = 1 := by
  simp

theorem amplitude_squared_ket1 : amplitude_squared |1⟩ = 1 := by
  simp

-- |00...0⟩ (= |0⟩ ⊗ ... ⊗ |0⟩ or the `n`-th tensor power of |0⟩).
def ket_zeros (n : ℕ) : Fin (2^n) → ℝ := fun i => if i = 0 then 1 else 0

notation "|0...0⟩" => ket_zeros

-- Show that |0...0⟩ equals |0⟩ ⊗ ... ⊗ |0⟩
-- Show that the amplitude squared of |0...0⟩ is 1
