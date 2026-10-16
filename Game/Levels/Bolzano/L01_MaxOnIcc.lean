import Game.Levels.Shade.L11_Boss

World "Bolzano"
Level 1

Introduction "Intro Bolzano L01"

open Set FullGrind

/-- A continuous function attains a maximum on a non-empty closed interval. -/
TheoremDoc exists_isMaxOn_Icc as "exists_isMaxOn_Icc" in "Bolzano"

Statement exists_isMaxOn_Icc {f : ℝ → ℝ} {a b : ℝ} (hf : Continuous f) (hab : a ≤ b) :
    ∃ x ∈ Icc a b, IsMaxOn f (Icc a b) x := by
  apply IsCompact.exists_isMaxOn isCompact_Icc _
  · fun_prop
  · simp [hab]

NewTheorem IsCompact.exists_isMaxOn

TheoremTab "Bolzano"
