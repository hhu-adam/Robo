import Game.Metadata

-- By Michel & Julia

World "Tmp"
Level 1

Title "Nullstellensatz"

Introduction
"
Der *Zwischenwertsatz* wird in der mathlib etwas abstrakter bewiesen:
Wenn man sich `intermediate_value_Icc` anschaut, enthält dieser noch
ganz viele Annahmen über

"

open Set Real

/-- The intermediate value theorem specialied to `ℝ`. -/
theorem Real.intermediate_value_Icc {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (f_cont : ContinuousOn f (Icc a b)) : Icc (f a) (f b) ⊆ f '' Icc a b :=
  _root_.intermediate_value_Icc hab f_cont

--NewTheorem Real.intermediate_value_Icc

-- Statement nullstellen_satz {a b : ℝ} (hab : a ≤ b) {f : ℝ  → ℝ}
--     (f_cont: ContinuousOn f (Icc a b)) (h₀ : (0 : ℝ) ∈ Icc (f a) (f b)) :
--     ∃ x ∈ Icc a b, f x = 0 := by
--   have iv := intermediate_value_Icc hab f_cont
--   -- TODO: Why does this work??
--   apply iv
--   assumption
