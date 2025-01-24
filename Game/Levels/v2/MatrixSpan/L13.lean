import Game.Metadata

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

import Game.Levels.MatrixSpan.L10

World "Span"
Level 13

Title "Span"

/- # Introduction

The universal property of the submodule `Submodule.span K S`  spanned by a set
`S : Set M` is that `x ∈ Submodule.span K S` iff `x ∈ P` for any submodule `P`
containing `S`.

-/

open Real Function Set Finset BigOperators

Statement powers_commute {n : ℕ} {A : Mat[n,n][ℝ]} (X Y : Mat[n,n][ℝ])
    (hX : X ∈ Submonoid.powers A)
    (hY : Y ∈ Submonoid.powers A) :
  X * Y = Y * X := by
  rw [Submonoid.mem_powers_iff] at *
  obtain ⟨m, rfl⟩ := hX
  obtain ⟨n, rfl⟩ := hY
  rw [← pow_add, ← pow_add, add_comm]
