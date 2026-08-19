import Game.Metadata

World "Bolzano"
Level 1

Introduction "Intro Bolzano L01"

open Set FullGrind

Statement exists_isMaxOn_Icc {f : ℝ → ℝ} {a b : ℝ} (hf : Continuous f) (hab : a ≤ b) :
    ∃ x ∈ Icc a b, IsMaxOn f (Icc a b) x := by
  apply IsCompact.exists_isMaxOn isCompact_Icc (nonempty_Icc.mpr hab)
  fun_prop

NewTheorem IsCompact.exists_isMaxOn Set.nonempty_Icc
