import Game.Metadata
import Game.Levels.MatrixSpan.L08

import Game.Levels.Robotswana

World "Span"
Level 9

Introduction "Intro Span L09"

open Real Function Set Finset BigOperators Matrix

Statement {n : ℕ} (A : Mat[n+2,n+2][ℝ]) :
    Submodule.span ℝ (Submonoid.powers A).carrier ≠ ⊤ := by
  intro hspan
  /- Here we could use `⟨n + 1, by grind⟩` instead of `⟨n + 1, (n + 1).lt_add_one⟩`. -/
  have h₁ : Matrix.E 0 ⟨n + 1, (n + 1).lt_add_one⟩ ∈
    Submodule.span ℝ (Submonoid.powers A).carrier := by
    rw [hspan]
    simp
  have h₂ : E ⟨n + 1, (n + 1).lt_add_one⟩ 0 ∈ Submodule.span ℝ (Submonoid.powers A).carrier := by
    rw [hspan]
    simp
  obtain h₃ := powers_span_commute h₁ h₂
  rw [Matrix.E.mul_same, Matrix.E.mul_same] at h₃
  obtain eq_aux := congr_fun₂ h₃ 0 0
  unfold E at eq_aux
  simp at eq_aux

/---/
TheoremDoc congr_fun₂ as "congr_fun₂" in "Function"

NewTheorem congr_fun₂

  -- part of old proof, broken.
  -- unfold single at this
  -- rw [if_neg] at this
  -- simp at *
  -- simp [Nat.succ_ne_zero]
  -- intro h
  -- norm_cast at h
  -- injection h
  -- simp at *
