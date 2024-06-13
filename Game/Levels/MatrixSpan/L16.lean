import Game.Metadata

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

import Game.Levels.MatrixSpan.L14
import Game.Levels.MatrixSpan.L15

import Game.Levels.MatrixTrace

World "Span"
Level 16

Title "Span"

/- # Introduction



-/

open Real Function Set Finset BigOperators Matrix

example {n : ℕ} (A : Mat[n+2,n+2][ℝ]) :
    Submodule.span ℝ (Submonoid.powers A).carrier ≠ ⊤ := by
  intro hspan
  have h₁ : Matrix.E 0 (n + 1) ∈ Submodule.span ℝ (Submonoid.powers A).carrier := by
    rw [hspan]
    simp only [Submodule.mem_top]
  have h₂ : E (n + 1) 0 ∈ Submodule.span ℝ (Submonoid.powers A).carrier := by
    rw [hspan]
    simp only [Submodule.mem_top]
  have h₃ := by apply powers_span_commute h₁ h₂
  rw [Matrix.E.mul_same, Matrix.E.mul_same] at h₃
  simp at h₃
  have := (congr_fun₂ h₃ 0 0)
  simp at this
  unfold E at this
  simp at this
  unfold stdBasisMatrix at this
  rw [if_neg] at this
  simp at *
  simp [Nat.succ_ne_zero]
  intro h
  norm_cast at h
  injection h
  simp at *
