import Game.Metadata




import Game.Levels.MatrixSpan.L08
import Game.Levels.MatrixSpan.L09

import Game.Levels.Robotswana

World "Span"
Level 10

Title "" -- "Span"

/- # Introduction



-/

open Real Function Set Finset BigOperators Matrix

Statement {n : ℕ} (A : Mat[n+2,n+2][ℝ]) :
    Submodule.span ℝ (Submonoid.powers A).carrier ≠ ⊤ := by
  intro hspan
  have h₁ : Matrix.E 0 ⟨n + 1, (n + 1).lt_add_one⟩ ∈
    Submodule.span ℝ (Submonoid.powers A).carrier := by
    rw [hspan]
    exact Submodule.mem_top
  have h₂ : E ⟨n + 1, (n + 1).lt_add_one⟩ 0 ∈ Submodule.span ℝ (Submonoid.powers A).carrier := by
    rw [hspan]
    exact Submodule.mem_top
  have h₃ := by
    apply powers_span_commute h₁ h₂
  rw [Matrix.E.mul_same, Matrix.E.mul_same] at h₃
  have := (congr_fun₂ h₃ 0 0)
  unfold E at this
  simp at this

  -- part of old proof, broken.
  -- unfold single at this
  -- rw [if_neg] at this
  -- simp at *
  -- simp [Nat.succ_ne_zero]
  -- intro h
  -- norm_cast at h
  -- injection h
  -- simp at *
