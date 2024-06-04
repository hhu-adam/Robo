import Game.Metadata

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

World "Span"
Level 8

Title "Span"

/- # Introduction

-/

open Real Function Set Finset BigOperators

Statement (M : Type*) [AddCommMonoid M] [Module ℝ M] (S : Submodule ℝ M) (x : M) (r : ℝ) (hr : r ≠ 0) :
    r • x ∈ S ↔ x ∈ S := by
  --apply Submodule.smul_mem_iff
  --assumption
  constructor
  · intro hrxS
    rw [← inv_smul_smul (Units.mk0 r hr) x]
    apply Submodule.smul_mem
    simpa using hrxS
  · intro hxS
    --simpa using (Submodule.smul_mem S r hxS)
    apply Submodule.smul_mem
    assumption
