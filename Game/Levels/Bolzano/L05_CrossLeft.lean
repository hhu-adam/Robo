import Game.Levels.Bolzano.L04_GetPreimage

World "Bolzano"
Level 5

Introduction "Intro Bolzano L05"

open Set FullGrind

/-- Suppose `f` vanishes at the left endpoint and takes the value `f m` at the right one. Then every value strictly between `0` and `f m` is attained strictly inside the interval. -/
TheoremDoc exists_mem_Ioo_eq_of_zero_left as "exists_mem_Ioo_eq_of_zero_left" in "Bolzano"

Statement exists_mem_Ioo_eq_of_zero_left {f : ℝ → ℝ} {a b m y : ℝ} (hf : Continuous f)
    (hab : a < b) (ha : f a = 0) (hb : f b = f m) (hy₀ : 0 < y) (hym : y < f m) :
    ∃ c ∈ Ioo a b, f c = y := by
  refine exists_mem_Ioo_eq hf hab ?_ ?_ ?_
  · apply mem_uIcc_of_le_of_le <;> grind
  · grind
  · grind

TheoremTab "Bolzano"
